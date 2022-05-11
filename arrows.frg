#lang forge

abstract sig Voter {
    firstChoice: one Candidate
}

sig Candidate {}

sig Lambda {}

one sig Election {
    winner: one Candidate,
    election_voters : set Voter,

    // The winner of an alternate universe election (where applicable)
    altWinner: one Candidate
}


//generic version of universality to prove that you can pass functions as arguments :,)

/* if every voter prefers A to B, then the group prefers A to B */
pred universality[allVotersPreferAtoB : Lambda, groupPreference : Lambda] { 
    all disj a,b : Candidate | allVotersPreferAtoB[a, b, Voter] implies groupPreference[a, b, Voter]
}

/* No voter exists such that if they changed their vote the entire outcome of the election would change */
pred noDictators {}

 /*
    If every voter's preference between X and Y remains unchanged,
    then the group's preference between X and Y will also remain unchanged
    (even if voters' preferences between other pairs like X and Z, Y and Z, or Z and W change).
*/
pred independenceOfIrrelevantAlternatives {}
