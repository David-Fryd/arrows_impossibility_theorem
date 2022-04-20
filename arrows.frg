#lang forge "arrow"

abstract sig Voter {
    firstChoice: one Candidate
}

// //sketched out just for vibes of where we're headed
// sig RCVVoter_Mandatory extends Voter {
//     secondChoice: one Candidate,
//     thirdChoice: one Candidate
// }

// sig RCVVoter_Optional extends Voter {
//     secondChoice: lone Candidate,
//     thirdChoice: lone Candidate
// }


sig Candidate {}

one sig Election {
    winner: one Candidate
}

pred noDictators { 
    no Voter | firstChoice changing changes outcome
    //no way for there to be an even number of votes assigned to two candidates, and then 1 more vote cast
}

pred universality { 
    //if everyone prefers A to B, then the group prefers A to B
}

pred independenceOfIrrelevantAlternatives {
    /*
    If every voter's preference between X and Y remains unchanged,
    then the group's preference between X and Y will also remain unchanged
    (even if voters' preferences between other pairs like X and Z, Y and Z, or Z and W change).
    */
}
