#lang forge

sig SimpleMajorityVoter extends Voter {}

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