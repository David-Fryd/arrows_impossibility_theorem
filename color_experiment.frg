abstract sig Color {
    my_color : one Color
}

one sig Result {
    result_color : one Color
}

one sig Blue extends Color {}

one sig Red extends Color {}

fun changeColor[a: Color]: one Color {
  (a.my_color = Red) 
  => Result.result_color = Blue
  else Result.result_color = Red
}

pred doMath[func_color : Color, c : Color] {
    func_color[c]
}

pred wellFormed {
    all b : Blue | b.my_color = Blue
    all r : Red | r.my_color = Red
}

run {
    wellFormed
    doMath[changeColor, Blue]
}