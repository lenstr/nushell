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
