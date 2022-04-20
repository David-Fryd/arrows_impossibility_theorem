#lang forge

abstract sig Color {
    my_color : one Color
}
abstract sig Weird {}

abstract sig Lambda {}

one sig Result {
    result_weird : one Weird
}

one sig Blue extends Color {}

one sig Red extends Color {}


one sig WeirdThingRed extends Weird{}
one sig WeirdThingBlue extends Weird {}

pred changeColor[a: Color] {
  (a.my_color = Red) 
   => Result.result_weird = WeirdThingRed
  else Result.result_weird = WeirdThingBlue
}

pred doSomething[func_color : Lambda, c : Color] {
    func_color[c]
}

pred wellFormed {
    all b : Blue | b.my_color = Blue
    all r : Red | r.my_color = Red
}

/*
    Both functions and predicates work as arguments, we may want to tell the argument that it's a Lambda, just for our
    knowledge, but apparently forge doesn't actually use these... it is just gonna throw it out
*/

run {
    wellFormed
    doSomething[changeColor, Blue]
}
