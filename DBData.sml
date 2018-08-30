structure DBData =
struct

val theory = fst o fst;

val name = snd o fst;

val theorem = fst o snd;

val class = snd o snd

end
