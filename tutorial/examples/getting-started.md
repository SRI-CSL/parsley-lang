# Getting Started

Let us first create a `.ply` file. We'll call it `dns.ply`.

The entire format is encapsulated around the `format { }` block. Your `ply` file should now look like this.

```
format {

}
```

Next, we create a nonterminal. We need to know two things over here, synthesized and inherited attributes. 

```
DNS d (l1: int, l2: int, l3: int, l4: int) {flag: int} := 
	n=Byte
	{d.flag := Int.of_byte(n)}
	;;
```

Let us dissect the above code snippet line by line.
- The nonterminal type is specified by the first word starting a production. Here, the nonterminal is `DNS`. This value needs to be in **camel-case**. Or at least start with a capital letter. 
- `d` is an object of type DNS.
- `(l1: int, l2: int, l3: int, l4: int)` these are inherited attributes. We will describe this in detail in a later section. 
- `{flag: int}` this is an assignment of a synthesized attribute. We can access this variable using the object assigned `d.flag` will give us access to this synthesized attribute. **In a single format, the synthesized attributes cannot overlap. For example, we can only have one flag.**
- RHS of the production begins with an `:=`.
- `n=Byte` this follows the syntax of data-dependent grammars. We create a variable in this context called `n`, which will contain all the attributes that the type `Byte` has.
- `{d.flag := Int.of_byte(n)} ` this is a synthesized attribute assignment. `Int.of_byte` is an in-built function in Parsley. We can convert a single byte to an Integer and test the value of this Integer easily this way. 
- The `;;` must only be used to separate two statements within a format. **If you have just one statement, you must not use `;;`**.

## Checking predicates on `n`

The predicates are enclosed in `[ ]`. For example, if in the above `DNS` snippet we were to test the value of `n` to be `1`, we would do the following.

```
[Int.of_byte(n) = 1]
```

Here we convert the byte to an integer, and then compare it to 1.

We can also create a predicate function of our own. For example,

```
fun between_one_five(b: [byte]) -> bool = {
1 <= Int.of_byte(b) && Int.of_byte(b) <= 5
}
[between_one_five(n)]
```

The functions must appear before the format descriptions begin.

## Literals

`a=!"SMITH"!` would match a string `"SMITH"`. `a` is now an array of bytes. 


## Repeat or Length field

We use the `^` syntax to repeat a nonterminal. For example, `X ^ Y` means that we repeat production `X`, `Y` times. We can easily use this syntax to apply both the repeat field and the length field.
In the snippet below, we extract the length field into the variable `len`, and then apply it to `Byte` in the variable `x`. This ensures that `x` is of length `len`. Since `len` is of type `byte`, we convert it to an `int` type.

```
format {

LengthValue v {b: [byte]} := 
len=Byte
x=(Byte ^ Int.of_byte(len))
}
```

If we want multiple bytes of the length field, we need to create a function to convert a byte string to an integer.
```
fun convert(b : [byte]) -> int = {                                                                                                                        
  (case Int.of_bytes(b) of                                                                                                                                
  | option::Some(i) -> i                                                                                                                                 
  | option::None()  -> 0)                                                                                                                                
}      
```
If the conversion does not encounter an error, it returns an integer. If it does encounter an error, it returns 0. We will have to change the production accordingly.

```
len=(Byte ^ 2)
x=(Byte ^ convert(len))   
```


