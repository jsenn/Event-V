# Snakes and Ladders
This example shows a formal model of the game [Snakes and Ladders](https://en.wikipedia.org/wiki/Snakes_and_ladders).

The [abstract model](abs.rs) abstracts the board away completely, tracking only its size. It also abstracts dice rolls away, but does track players' positions and whose turn it is. At each turn, the player is teleported to some arbitrary board position.

The [refined model](board.rs) introduces dice rolls and a model of the board, including the snakes and ladders mechanics. It defines what counts as a valid board, proves that every game on a valid board is winnable, and implements the full mechanics of a turn: roll dice, follow snakes and ladders, landing on a square somewhere else on the board.