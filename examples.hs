If coNP subset NP then NP subet coNP

C(x,y)    x and y are complements of each other
CNP = coNP

Enter goal formula X > all x all y (C(x,y) & NP(x) -> CNP(y)) -> all x (CNP(x) -> NP(x)) -> all x all y(C(x,y) -> C(y,x)) -> all x ex y C(x,y) -> all x (NP(x) -> CNP(x))
Enter command> impi u1
Enter command> impi u2
Enter command> impi u3
Enter command> impi u4
Enter command> alli
Enter command> impi u5
Enter command> exe ex y C(x,y)
Enter command> alle e y
Enter command> use ue
Enter command> alli
Enter command> impi u6
Enter command> impe C(y,x) & NP(y)
Enter command> impi u7
Enter command> undo
Enter command> alle x
Enter command> alle y
Enter command> use u1
Enter command> andi
Enter command> impe C(x,y)
Enter command> alle y
Enter command> alle x
Enter command> use u3
Enter command> use u6
Enter command> impe CNP(y)
Enter command> alle y
Enter command> use u2
Enter command> impe C(x,y) & NP(x)
Enter command> alle y
Enter command> alle x
Enter command> use u1
Enter command> andi
Enter command> use u6
Enter command> use u5
Proof complete.
