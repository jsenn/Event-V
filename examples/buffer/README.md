# Buffer Example
This example shows a simple model of a fixed-size buffer.

The [abstract model](buf0.rs) tracks only the buffer's current size, abstracting the actual contents away completely. It introduces abstract versions of the 3 main operations on the buffer: **Put**, **Fetch**, and **GetSize**.

The [refined model](buf1.rs) adds the buffer's contents (assumed for simplicity to be a sequence of natural numbers).

# See Also
This example was adapted from [Lean Machines](https://github.com/lean-machines-central/lean-machines-examples/tree/main/LeanMachinesExamples/Buffer).