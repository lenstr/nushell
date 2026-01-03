def test-cmd [
    --flag: int
    --other: string
    -s: int  # short flag only
] {
    print $flag
}

test-cmd --flag 42
test-cmd --other "hello"
test-cmd -s 10

# Test dash-to-underscore conversion
def cmd-with-dashed-flag [
    --some-flag: string
] {
    print $some_flag
}

cmd-with-dashed-flag --some-flag "test"
