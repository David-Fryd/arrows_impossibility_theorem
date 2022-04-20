#lang forge

sig SimpleMajorityVoter extends Voter {}

// abstract sig Color {
//     my_color : one Color
// }

// one sig Result {
//     result_color : one Color
// }

// one sig Blue extends Color {
// }

// one sig Red extends Color {
// }

// fun changeColor[a: Color]: one Color {
//   (a.my_color = Red) 
//   => Result.result_color = Blue
//   else Result.result_color = Red
// }

// pred doMath[func_color : Color, c : Color] {
//     func_color[c]
// }

// pred wellFormed {
//     all b : Blue | b.my_color = Blue
//     all r : Red | r.my_color = Red
// }

// run {
//     wellFormed
//     doMath[changeColor, Blue]
// }

pred determineWinnerSimpleMajority {
    /*
        Count up the votes for each candidate
        Say winner is the winner
    */
}

pred noDictatorsSM { 
    //no Voter | firstChoice changing changes outcome
    //no way for there to be an even number of votes assigned to two candidates, and then 1 more vote cast
}

pred universalitySM { 
    //if everyone prefers A to B, then the group prefers A to B
}

pred independenceOfIrrelevantAlternativesSM {
    /*
    If every voter's preference between X and Y remains unchanged,
    then the group's preference between X and Y will also remain unchanged
    (even if voters' preferences between other pairs like X and Z, Y and Z, or Z and W change).
    */
}