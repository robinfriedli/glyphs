# glyphs

Object-oriented and statically typed programming language compiled to JVM bytecode with a syntax that is heavily inspired by Rust.

A sample hello work project could look like this:

```
class Foo {
    x: int;

    constructor(x: int) {
        this.x = x;
    }

    fn do_something(a: int, b: boolean) -> int {
        if (b) {
            return this.x * a;
        } else {
            return this.x + a;
        }
    }
}

class Bar: Foo {

    constructor(x: int) {
        super(x);
    }

    override fn do_something(a: int, b: boolean) -> int {
        return super.do_something(a, b) * 2;
    }

}

class Main {
    fn main(args: String[]) {
        let x = 2;
        let y: long = 4;
        let bar = new Bar(x);
        print("Hello World " + bar.do_something(y as int, false));
    }
}

```
