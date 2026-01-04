use crate::Id;
use nu_protocol::{
    DeclId, ModuleId, Span, VarId,
    ast::{Argument, Block, Call, Expr, Expression, FindMapResult, ListItem, PathMember, Traverse},
    engine::StateWorkingSet,
};
use std::sync::Arc;

/// Adjust span if quoted
fn strip_quotes(span: Span, working_set: &StateWorkingSet) -> (Box<[u8]>, Span) {
    let text = working_set.get_span_contents(span);
    if text.len() > 1
        && ((text.starts_with(b"\"") && text.ends_with(b"\""))
            || (text.starts_with(b"'") && text.ends_with(b"'")))
    {
        (
            text.get(1..text.len() - 1)
                .expect("Invalid quoted span!")
                .into(),
            Span::new(span.start.saturating_add(1), span.end.saturating_sub(1)),
        )
    } else {
        (text.into(), span)
    }
}

/// Trim leading `$` sign For variable references `$foo`
fn strip_dollar_sign(span: Span, working_set: &StateWorkingSet<'_>) -> (Box<[u8]>, Span) {
    let content = working_set.get_span_contents(span);
    if content.starts_with(b"$") {
        (
            content[1..].into(),
            Span::new(span.start.saturating_add(1), span.end),
        )
    } else {
        (content.into(), span)
    }
}

/// For a command call with head span content of `module name command    name`,
/// return the span of `command    name`,
/// while the actual command name is simply `command name`
fn command_name_span_from_call_head(
    working_set: &StateWorkingSet,
    decl_id: DeclId,
    head_span: Span,
) -> Span {
    let name = working_set.get_decl(decl_id).name();
    // shortcut for most cases
    if name.len() == head_span.end.saturating_sub(head_span.start) {
        return head_span;
    }
    let head_content = working_set.get_span_contents(head_span);
    let mut head_words = head_content.split(|c| *c == b' ').collect::<Vec<_>>();
    let mut name_words = name.split(' ').collect::<Vec<_>>();
    let mut matched_len = name_words.len() - 1;
    while let Some(name_word) = name_words.pop() {
        while let Some(head_word) = head_words.pop() {
            // for extra spaces, like those in the `command    name` example
            if head_word.is_empty() && !name_word.is_empty() {
                matched_len += 1;
                continue;
            }
            if name_word.as_bytes() == head_word {
                matched_len += head_word.len();
                break;
            } else {
                // no such command name substring in head span
                // probably an alias command, returning the whole head span
                return head_span;
            }
        }
        if name_words.len() > head_words.len() {
            return head_span;
        }
    }
    Span::new(head_span.end.saturating_sub(matched_len), head_span.end)
}

fn try_find_id_in_misc(
    call: &Call,
    working_set: &StateWorkingSet,
    location: Option<&usize>,
    id_ref: Option<&Id>,
) -> Option<(Id, Span)> {
    let call_name = working_set.get_decl(call.decl_id).name();
    match call_name {
        "def" | "export def" => try_find_id_in_def(call, working_set, location, id_ref),
        "module" | "export module" => try_find_id_in_mod(call, working_set, location, id_ref),
        "use" | "export use" | "hide" => try_find_id_in_use(call, working_set, location, id_ref),
        "overlay use" | "overlay hide" => {
            try_find_id_in_overlay(call, working_set, location, id_ref)
        }
        _ => None,
    }
}

/// For situations like
/// ```nushell
/// def foo [] {}
///    # |__________ location
/// ```
/// `def` is an internal call with name/signature/closure as its arguments
///
/// # Arguments
/// - `location`: None if no `contains` check required
/// - `id`: None if no id equal check required
fn try_find_id_in_def(
    call: &Call,
    working_set: &StateWorkingSet,
    location: Option<&usize>,
    id_ref: Option<&Id>,
) -> Option<(Id, Span)> {
    // skip if the id to search is not a declaration id
    if let Some(id_ref) = id_ref
        && !matches!(id_ref, Id::Declaration(_))
    {
        return None;
    }
    let mut span = None;
    for arg in call.arguments.iter() {
        if location.is_none_or(|pos| arg.span().contains(*pos)) {
            // String means this argument is the name
            if let Argument::Positional(expr) = arg
                && let Expr::String(_) = &expr.expr
            {
                span = Some(expr.span);
                break;
            }
            // if we do care the location,
            // reaching here means this argument is not the name
            if location.is_some() {
                return None;
            }
        }
    }

    let block_span_of_this_def = call.positional_iter().last()?.span;
    let decl_on_spot = |decl_id: &DeclId| -> bool {
        working_set
            .get_decl(*decl_id)
            .block_id()
            .and_then(|block_id| working_set.get_block(block_id).span)
            .is_some_and(|block_span| block_span == block_span_of_this_def)
    };

    let (_, span) = strip_quotes(span?, working_set);
    let id_found = if let Some(id_r) = id_ref {
        let Id::Declaration(decl_id_ref) = id_r else {
            return None;
        };
        decl_on_spot(decl_id_ref).then_some(id_r.clone())?
    } else {
        // Find declaration by name, e.g. `workspace.find_decl`, is not reliable
        // considering shadowing and overlay prefixes
        // TODO: get scope by position
        // https://github.com/nushell/nushell/issues/15291
        Id::Declaration((0..working_set.num_decls()).rev().find_map(|id| {
            let decl_id = DeclId::new(id);
            decl_on_spot(&decl_id).then_some(decl_id)
        })?)
    };
    Some((id_found, span))
}

/// For situations like
/// ```nushell
/// module foo {}
///       # |__________ location
/// ```
/// `module` is an internal call with name/signature/closure as its arguments
///
/// # Arguments
/// - `location`: None if no `contains` check required
/// - `id`: None if no id equal check required
fn try_find_id_in_mod(
    call: &Call,
    working_set: &StateWorkingSet,
    location: Option<&usize>,
    id_ref: Option<&Id>,
) -> Option<(Id, Span)> {
    // skip if the id to search is not a module id
    if let Some(id_ref) = id_ref
        && !matches!(id_ref, Id::Module(_, _))
    {
        return None;
    }

    let check_location = |span: &Span| location.is_none_or(|pos| span.contains(*pos));
    call.arguments.first().and_then(|arg| {
        if !check_location(&arg.span()) {
            return None;
        }
        match arg {
            Argument::Positional(expr) => {
                let name = expr.as_string()?;
                let module_id = working_set.find_module(name.as_bytes()).or_else(|| {
                    // in case the module is hidden
                    let mut any_id = true;
                    let mut id_num_ref = 0;
                    if let Some(Id::Module(id_ref, _)) = id_ref {
                        any_id = false;
                        id_num_ref = id_ref.get();
                    }
                    let block_span = call.arguments.last()?.span();
                    (0..working_set.num_modules())
                        .rfind(|id| {
                            (any_id || id_num_ref == *id)
                                && working_set.get_module(ModuleId::new(*id)).span.is_some_and(
                                    |mod_span| {
                                        mod_span.start <= block_span.start + 1
                                            && block_span.start <= mod_span.start
                                            && block_span.end >= mod_span.end
                                            && block_span.end <= mod_span.end + 1
                                    },
                                )
                        })
                        .map(ModuleId::new)
                })?;
                let found_id = Id::Module(module_id, name.as_bytes().into());
                let found_span = strip_quotes(arg.span(), working_set).1;
                id_ref
                    .is_none_or(|id_r| found_id == *id_r)
                    .then_some((found_id, found_span))
            }
            _ => None,
        }
    })
}

/// Find id in use/hide command
/// `hide foo.nu bar` or `use foo.nu [bar baz]`
///
/// # Arguments
/// - `location`: None if no `contains` check required
/// - `id`: None if no id equal check required
fn try_find_id_in_use(
    call: &Call,
    working_set: &StateWorkingSet,
    location: Option<&usize>,
    id_ref: Option<&Id>,
) -> Option<(Id, Span)> {
    // NOTE: `call.parser_info` contains a 'import_pattern' field for `use`/`hide` commands,
    // If it's missing, usually it means the PWD env is not correctly set,
    // checkout `new_engine_state` in lib.rs
    let Expression {
        expr: Expr::ImportPattern(import_pattern),
        ..
    } = call.get_parser_info("import_pattern")?
    else {
        return None;
    };
    let module_id = import_pattern.head.id?;

    let find_by_name = |name: &[u8]| {
        let module = working_set.get_module(module_id);
        match id_ref {
            Some(Id::Variable(var_id_ref, name_ref)) => module
                .constants
                .get(name)
                .cloned()
                .or_else(|| {
                    // NOTE: This is for the module record variable:
                    // https://www.nushell.sh/book/modules/using_modules.html#importing-constants
                    // The definition span is located at the head of the `use` command.
                    (name_ref.as_ref() == name
                        && call
                            .head
                            .contains_span(working_set.get_variable(*var_id_ref).declaration_span))
                    .then_some(*var_id_ref)
                })
                .and_then(|var_id| {
                    (var_id == *var_id_ref).then_some(Id::Variable(var_id, name.into()))
                }),
            Some(Id::Declaration(decl_id_ref)) => module.decls.get(name).and_then(|decl_id| {
                (*decl_id == *decl_id_ref).then_some(Id::Declaration(*decl_id))
            }),
            // this is only for argument `members`
            Some(Id::Module(module_id_ref, name_ref)) => {
                module.submodules.get(name).and_then(|module_id| {
                    (*module_id == *module_id_ref && name_ref.as_ref() == name)
                        .then_some(Id::Module(*module_id, name.into()))
                })
            }
            None => module
                .submodules
                .get(name)
                .map(|id| Id::Module(*id, name.into()))
                .or(module.decls.get(name).cloned().map(Id::Declaration))
                .or(module
                    .constants
                    .get(name)
                    .map(|id| Id::Variable(*id, name.into()))),
            _ => None,
        }
    };
    let check_location = |span: &Span| location.is_none_or(|pos| span.contains(*pos));

    // Get module id if required
    let module_name = call.arguments.first()?;
    let span = module_name.span();
    let (span_content, clean_span) = strip_quotes(span, working_set);
    if let Some(Id::Module(id_ref, name_ref)) = id_ref {
        // still need to check the rest, if id not matched
        if module_id == *id_ref && name_ref == &span_content {
            return Some((Id::Module(module_id, span_content), clean_span));
        }
    }
    if let Some(pos) = location {
        // first argument of `use`/`hide` should always be module name
        if span.contains(*pos) {
            return Some((Id::Module(module_id, span_content), clean_span));
        }
    }

    let search_in_list_items = |items: &Vec<ListItem>| {
        items.iter().find_map(|item| {
            let item_expr = item.expr();
            check_location(&item_expr.span)
                .then_some(item_expr)
                .and_then(|e| {
                    let name = e.as_string()?;
                    Some((
                        find_by_name(name.as_bytes())?,
                        strip_quotes(item_expr.span, working_set).1,
                    ))
                })
        })
    };

    for arg in call.arguments.get(1..)?.iter().rev() {
        let Argument::Positional(expr) = arg else {
            continue;
        };
        if !check_location(&expr.span) {
            continue;
        }
        let matched = match &expr.expr {
            Expr::String(name) => {
                find_by_name(name.as_bytes()).map(|id| (id, strip_quotes(expr.span, working_set).1))
            }
            Expr::List(items) => search_in_list_items(items),
            Expr::FullCellPath(fcp) => {
                let Expr::List(items) = &fcp.head.expr else {
                    return None;
                };
                search_in_list_items(items)
            }
            _ => None,
        };
        if matched.is_some() || location.is_some() {
            return matched;
        }
    }
    None
}

/// Find id in use/hide command
///
/// TODO: rename of `overlay use as new_name`, `overlay use --prefix`
///
/// # Arguments
/// - `location`: None if no `contains` check required
/// - `id`: None if no id equal check required
fn try_find_id_in_overlay(
    call: &Call,
    working_set: &StateWorkingSet,
    location: Option<&usize>,
    id_ref: Option<&Id>,
) -> Option<(Id, Span)> {
    // skip if the id to search is not a module id
    if let Some(id_ref) = id_ref
        && !matches!(id_ref, Id::Module(_, _))
    {
        return None;
    }
    let check_location = |span: &Span| location.is_none_or(|pos| span.contains(*pos));
    let module_from_parser_info = |span: Span, name: &str| {
        let Expression {
            expr: Expr::Overlay(Some(module_id)),
            ..
        } = call.get_parser_info("overlay_expr")?
        else {
            return None;
        };
        let found_id = Id::Module(*module_id, name.as_bytes().into());
        id_ref
            .is_none_or(|id_r| found_id == *id_r)
            .then_some((found_id, strip_quotes(span, working_set).1))
    };
    // NOTE: `overlay_expr` doesn't exist for `overlay hide`
    let module_from_overlay_name = |name: &str, span: Span| {
        let found_id = Id::Module(
            working_set.find_overlay(name.as_bytes())?.origin,
            name.as_bytes().into(),
        );
        id_ref
            .is_none_or(|id_r| found_id == *id_r)
            .then_some((found_id, strip_quotes(span, working_set).1))
    };

    // check `as alias` first
    for arg in call.arguments.iter().rev() {
        let Argument::Positional(expr) = arg else {
            continue;
        };
        if !check_location(&expr.span) {
            continue;
        };
        let matched = match &expr.expr {
            Expr::String(name) => module_from_parser_info(expr.span, name)
                .or_else(|| module_from_overlay_name(name, expr.span)),
            // keyword 'as'
            Expr::Keyword(kwd) => match &kwd.expr.expr {
                Expr::String(name) => module_from_parser_info(kwd.expr.span, name)
                    .or_else(|| module_from_overlay_name(name, kwd.expr.span)),
                _ => None,
            },
            _ => None,
        };
        if matched.is_some() || location.is_some() {
            return matched;
        }
    }
    None
}

/// Find a named argument (flag) in a call
///
/// # Arguments
/// - `location`: cursor position for go-to-definition, None for find-references
/// - `id_ref`: target ID for find-references, None for go-to-definition
fn try_find_id_in_flag(
    call: &Call,
    working_set: &StateWorkingSet,
    location: Option<&usize>,
    id_ref: Option<&Id>,
) -> Option<(Id, Span)> {
    let check_location = |span: &Span| location.is_none_or(|pos| span.contains(*pos));

    for arg in &call.arguments {
        if let Argument::Named((name, short_form, _)) = arg {
            // Check the primary flag name (--flag or -f)
            if check_location(&name.span)
                && let Some(id) =
                    find_flag_var_id(working_set, call.decl_id, name.item.trim_start_matches('-'))
                && id_ref.is_none_or(|r| *r == id)
            {
                return Some((id, name.span));
            }
            // Check explicit short flag (-f in "--flag -f")
            if let Some(short) = short_form
                && check_location(&short.span)
                && let Some(short_char) = short.item.chars().last()
                && let Some(id) = find_short_flag_var_id(working_set, call.decl_id, short_char)
                && id_ref.is_none_or(|r| *r == id)
            {
                return Some((id, short.span));
            }
        }
    }
    None
}

/// Find flag's variable Id by its long name
fn find_flag_var_id(working_set: &StateWorkingSet, decl_id: DeclId, flag_name: &str) -> Option<Id> {
    let signature = working_set.get_decl(decl_id).signature();
    signature.named.iter().find_map(|flag| {
        if flag.long != flag_name {
            return None;
        }
        let var_id = flag.var_id?;
        // Get the actual variable name from declaration span (handles dash to underscore conversion)
        let name = get_var_name_from_declaration(working_set, var_id);
        Some(Id::Variable(var_id, name))
    })
}

/// Find flag's variable Id by its short char
fn find_short_flag_var_id(
    working_set: &StateWorkingSet,
    decl_id: DeclId,
    short_char: char,
) -> Option<Id> {
    let signature = working_set.get_decl(decl_id).signature();
    signature.named.iter().find_map(|flag| {
        if flag.short != Some(short_char) {
            return None;
        }
        let var_id = flag.var_id?;
        // Get the actual variable name from declaration span (handles dash to underscore conversion)
        let name = get_var_name_from_declaration(working_set, var_id);
        Some(Id::Variable(var_id, name))
    })
}

/// Get the variable name from its declaration span
fn get_var_name_from_declaration(working_set: &StateWorkingSet, var_id: VarId) -> Box<[u8]> {
    let var = working_set.get_variable(var_id);
    let content = working_set.get_span_contents(var.declaration_span);
    // Strip leading dashes if present (for flag declarations like --flag or -f)
    content
        .strip_prefix(b"--")
        .or_else(|| content.strip_prefix(b"-"))
        .unwrap_or(content)
        .into()
}

/// Find a flag or parameter definition in a signature expression
///
/// # Arguments
/// - `signature`: The signature to search in
/// - `working_set`: The working set for looking up variables
/// - `location`: cursor position for go-to-definition, None for find-references
/// - `id_ref`: target ID for find-references, None for go-to-definition
fn try_find_id_in_signature(
    signature: &nu_protocol::Signature,
    working_set: &StateWorkingSet,
    location: Option<&usize>,
    id_ref: Option<&Id>,
) -> Option<(Id, Span)> {
    let check_location = |span: &Span| location.is_none_or(|pos| span.contains(*pos));

    // Check flags (named parameters)
    signature
        .named
        .iter()
        .find_map(|flag| {
            let var_id = flag.var_id?;
            let var = working_set.get_variable(var_id);
            let decl_span = var.declaration_span;
            if !check_location(&decl_span) {
                return None;
            }
            let name = get_var_name_from_declaration(working_set, var_id);
            let id = Id::Variable(var_id, name);
            id_ref.is_none_or(|r| *r == id).then_some((id, decl_span))
        })
        .or_else(|| {
            // Check positional parameters
            signature
                .required_positional
                .iter()
                .chain(signature.optional_positional.iter())
                .chain(signature.rest_positional.iter())
                .find_map(|positional| {
                    let var_id = positional.var_id?;
                    let var = working_set.get_variable(var_id);
                    let decl_span = var.declaration_span;
                    if !check_location(&decl_span) {
                        return None;
                    }
                    let content = working_set.get_span_contents(decl_span);
                    let id = Id::Variable(var_id, content.into());
                    id_ref.is_none_or(|r| *r == id).then_some((id, decl_span))
                })
        })
}

fn find_id_in_expr(
    expr: &Expression,
    working_set: &StateWorkingSet,
    location: &usize,
) -> FindMapResult<(Id, Span)> {
    // skip the entire expression if the location is not in it
    if !expr.span.contains(*location) {
        return FindMapResult::Stop;
    }
    let span = expr.span;
    match &expr.expr {
        Expr::VarDecl(var_id) | Expr::Var(var_id) => {
            let (name, clean_span) = strip_dollar_sign(span, working_set);
            FindMapResult::Found((Id::Variable(*var_id, name), clean_span))
        }
        Expr::Call(call) => {
            if call.head.contains(*location) {
                let span = command_name_span_from_call_head(working_set, call.decl_id, call.head);
                FindMapResult::Found((Id::Declaration(call.decl_id), span))
            } else {
                try_find_id_in_flag(call, working_set, Some(location), None)
                    .or_else(|| try_find_id_in_misc(call, working_set, Some(location), None))
                    .map(FindMapResult::Found)
                    .unwrap_or_default()
            }
        }
        Expr::ExternalCall(head, _) => {
            if head.span.contains(*location)
                && let Expr::GlobPattern(cmd, _) = &head.expr
            {
                return FindMapResult::Found((Id::External(cmd.clone()), head.span));
            }
            FindMapResult::Continue
        }
        Expr::FullCellPath(fcp) => {
            if fcp.head.span.contains(*location) {
                FindMapResult::Continue
            } else {
                let Expression {
                    expr: Expr::Var(var_id),
                    ..
                } = fcp.head
                else {
                    return FindMapResult::Continue;
                };
                let tail: Vec<PathMember> = fcp
                    .tail
                    .clone()
                    .into_iter()
                    .take_while(|pm| pm.span().start <= *location)
                    .collect();
                let Some(span) = tail.last().map(|pm| pm.span()) else {
                    return FindMapResult::Stop;
                };
                FindMapResult::Found((Id::CellPath(var_id, tail), span))
            }
        }
        Expr::Overlay(Some(module_id)) => {
            FindMapResult::Found((Id::Module(*module_id, [].into()), span))
        }
        Expr::Signature(sig) => {
            // Check if the cursor is on a flag/parameter definition within the signature
            if let Some(result) = try_find_id_in_signature(sig, working_set, Some(location), None) {
                FindMapResult::Found(result)
            } else {
                FindMapResult::Found((Id::Value(expr.ty.clone()), span))
            }
        }
        // terminal value expressions
        Expr::Bool(_)
        | Expr::Binary(_)
        | Expr::DateTime(_)
        | Expr::Directory(_, _)
        | Expr::Filepath(_, _)
        | Expr::Float(_)
        | Expr::Garbage
        | Expr::GlobPattern(_, _)
        | Expr::Int(_)
        | Expr::Nothing
        | Expr::RawString(_)
        | Expr::String(_) => FindMapResult::Found((Id::Value(expr.ty.clone()), span)),
        _ => FindMapResult::Continue,
    }
}

/// find the leaf node at the given location from ast
pub(crate) fn find_id(
    ast: &Arc<Block>,
    working_set: &StateWorkingSet,
    location: &usize,
) -> Option<(Id, Span)> {
    let closure = |e| find_id_in_expr(e, working_set, location);
    ast.find_map(working_set, &closure)
}

fn find_reference_by_id_in_expr(
    expr: &Expression,
    working_set: &StateWorkingSet,
    id: &Id,
) -> Vec<Span> {
    match (&expr.expr, id) {
        (Expr::Var(vid1), Id::Variable(vid2, _)) if *vid1 == *vid2 => vec![Span::new(
            // we want to exclude the `$` sign for renaming
            expr.span.start.saturating_add(1),
            expr.span.end,
        )],
        (Expr::VarDecl(vid1), Id::Variable(vid2, _)) if *vid1 == *vid2 => vec![expr.span],
        // also interested in `var_id` in call.arguments of `use` command
        // and `module_id` in `module` command
        (Expr::Call(call), _) => match id {
            Id::Declaration(decl_id) if call.decl_id == *decl_id => {
                vec![command_name_span_from_call_head(
                    working_set,
                    call.decl_id,
                    call.head,
                )]
            }
            // Check for flag references and misc matches (use, module, etc.)
            _ => try_find_id_in_flag(call, working_set, None, Some(id))
                .map(|(_, span)| span)
                .into_iter()
                .chain(try_find_id_in_misc(call, working_set, None, Some(id)).map(|(_, span)| span))
                .collect(),
        },
        // NOTE: We don't need to handle Expr::Signature here because
        // reference_not_in_ast already adds the definition span.
        // The definition in the signature is handled specially because
        // it needs span adjustment (stripping dashes).
        _ => vec![],
    }
}

pub(crate) fn find_reference_by_id(
    ast: &Arc<Block>,
    working_set: &StateWorkingSet,
    id: &Id,
) -> Vec<Span> {
    let mut results = Vec::new();
    let closure = |e| find_reference_by_id_in_expr(e, working_set, id);
    ast.flat_map(working_set, &closure, &mut results);
    results
}
