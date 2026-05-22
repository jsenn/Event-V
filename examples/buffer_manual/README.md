# Buffer (manual version)
This shows an equivalent of the [buffer example](../buffer/) but without using the macro syntax. Instead, the full trait machinery of Event-V is spelled out manually. There are pros and cons of this workflow.

Pros:
* Explicit, normal Rust/Verus with no special syntax to remember
* To a large extent, Rust/Verus will guide you on what you need to do next with compiler and verification errors
* Rust Analyzer can often generate the boilerplate for you

Cons:
* It is very verbose
* The logic of the spec is harder to read