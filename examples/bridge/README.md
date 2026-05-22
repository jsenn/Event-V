# Bridge Example
This example shows a full implementation of the bridge controller spec from chapter 2 of the book [Modeling in Event-B](https://doi.org/10.1017/CBO9781139195881).

The basic setup is an island separated from the mainland by a bridge. Cars travel to and from the island over the bridge. The main constraints of the system are:
1. There is a maximum number of cars allowed on the island at any given time.
2. The bridge is one-way--that is, cars may be travelling to the island or from the island at any given time, but not both directions at once.

The [abstract model](abs.rs) ignores the bridge, tracking only the number of cars on the island.

The [first refinement](ref1.rs) adds the bridge, tracking the number of cars travelling to the island, from the island, and the number currently on the island.

The [second refinement](ref2.rs) adds traffic lights to the system to prevent cars from entering the bridge when it would violate the one-way requirement.

Finally, the [third refinement](ref3.rs) introduces sensors to the system, and separates the model of the bridge **controller** from the model of the **environment**. From the controller spec, a full executable implementation can be derived.

# See Also
Lean Machines has [a similar example](https://github.com/lean-machines-central/lean-machines-examples/tree/main/LeanMachinesExamples/EventB/Bridge) showing the abstract machine and the first 2 refinements.