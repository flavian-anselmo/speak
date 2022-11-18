## Types
### Numbers
Unsigned integers:
- `uint8`
- `uint16`
- `uint32`
- `uint64`

Signed integers:
- `int8`
- `int16`
- `int32`
- `int64`

### Strings
A `char` is a unicode character, it is an alias for uint8. A uint8 can be cast to a `char`
A `string` is an alias for `[]uint8`.

### Booleans
- `true`
- `false`

Operations:
- `&` and
- `|` or
- `~` not


## Functions

The function definition starts with the function name followed by colons, `:`.
The `main` function has no arguements and does not return anything.
It is called by the program and needs not be called explicitly.

`main` is a keyword reserved for the main fucntion declaration.

```sp
main:
    fmt::print "Hello World!"
```

Returning from `speak` requires that the `=` symbol is used such that there should be no variable on the LHS.
```sp
-- Compute the sum
sum: a int, b int -> int = a +b
```

The function parameters should be named in order to reference them.
When more than two parameters are provided and one is unamed, the `_` is used.
If neither parameter is used, both remain unamed.
```sp
-- Compute the sum
sum: a, b int -> int = a + b

jumla: a, b namb -> namb = a + b

-- Given a and b, return a
ret_a: a, _ int -> int = a

```

``` sp
mod "fmt"

-- print_hi prints "Hi!"
print_hi: int, int = fmt::print "Hi!"


-- Trying out a closure
this:
    m := a, b int -> int = a +b
    fmt::print m 1 2
```


```sp
f: int, int -> int
main

```

```sp
struct Person
```
