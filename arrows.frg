#lang forge

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

sig Lambda {}

one sig Election {
    winner: one Candidate,
    election_voters : set Voter
}


pred abstractDetermineWinner[func_winner : Lambda] {
    func_winner
}

pred noDictators { 
    
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
