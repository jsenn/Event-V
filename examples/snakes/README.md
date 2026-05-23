# Snakes and Ladders
This example shows a formal model of the game [Snakes and Ladders](https://en.wikipedia.org/wiki/Snakes_and_ladders).

The [abstract model](abs.rs) abstracts the board away completely, tracking only its size. It also abstracts dice rolls away, but does track players' positions and whose turn it is. At each turn, the player is teleported to some arbitrary board position.

The [board representation](board.rs) used in the refined model is factored out. It defines what counts as a valid board, proves that every valid snaeks and ladders board is winnable, and provides some useful helper functions.

The [refined model](snakes.rs) introduces dice rolls and uses the full board representation.