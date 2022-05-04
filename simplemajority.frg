#lang forge
open "arrows.frg"


//may add hidden preferences to 
sig SimpleMajorityVoter extends Voter {
   hiddenSecondChoice: one Candidate,
   hiddenThirdChoice: one Candidate
}


/*
    Anticipate issues with Election.election_voters/any set of voters/choices of voters changing between calls? 
*/
pred wellformed {
    #Candidate = 3
    #SimpleMajorityVoter > #Candidate
    all v : Voter | v in SimpleMajorityVoter
    Election.election_voters = Voter
    all v : Voter | (v.firstChoice != v.hiddenSecondChoice) and (v.firstChoice != v.hiddenThirdChoice) (v.hiddenSecondChoice != v.hiddenThirdChoice)
}

/* enforces that the winner of the election has the most votes */
pred isSimpleMajorityWinner[c : Candidate] { //todo: take in a set of simplemajority voters
    all other_c : Candidate | other_c != c implies {
        #{sv : SimpleMajorityVoter | sv.firstChoice = c} > #{sv : SimpleMajorityVoter | sv.firstChoice = other_c}
    }
}

// TODO: Replace the original [isSimpleMajorityWinner] eventually
pred isSimpleMajorityWinnerAbstractVersion[c : Candidate] { //todo: take in a set of simplemajority voters
    all other_c : Candidate | other_c != c implies {
        #{sv : SimpleMajorityVoter | sv.firstChoice = c} > #{sv : SimpleMajorityVoter | sv.firstChoice = other_c}
    }
}

pred thereIsAWinner {
    some c : Candidate | isSimpleMajorityWinner[c] and Election.winner = c
}

//TODO: rename this getSimpleMajorityWinner?
fun mostFirstChoiceVotes[e : Election]: one Candidate {
    e.winner
}

pred noDictatorsSM { 
    //no Voter | firstChoice changing changes outcome
    //no way for there to be an even number of votes assigned to two candidates, and then 1 more vote cast
    // isSimpleMajorityWinnerAbstractVersion doesnt change when a single person's first choice changes
}


pred smHasPrefForA[a : Candidate, b : Candidate, v : Voter] {
    v.firstChoice = a
    // for simple majority, implicitly v.firstChoice != b
}

pred smAllVotersPreferAtoB[a : Candidate, b : Candidate, voterSet: set Voter] {
    all v: Voter | v in voterSet implies {
        smHasPrefForA[a,b,v]
    }
}

pred smGroupPreference[a : Candidate, b : Candidate, voterSet: set Voter] {
    #{vot : Voter | vot in voterSet and vot.firstChoice = a} > #{vot : Voter | vot in voterSet and vot.firstChoice = b}
}

// TODO: Eventually just "pred universality" that works for all systems,
// TODO: Pass in a "hasPreferenceForA" fxn dependent on the voting system itself
pred universalitySM { 
    // For simple majority, its a bit tautologic, but thats what impossibility translates to here
    //if everyone prefers A to B, then the group prefers A to B
    all disj a,b : Candidate | smAllVotersPreferAtoB[a, b, Voter] implies smGroupPreference[a, b, Voter]
        //#{v : Voter | v.firstChoice = a} > #{v : Voter | v.firstChoice = b}
        /**
        groupPreference[a,b,V] implies allVoterspreferAtoB[a,b,V] ?
        (i guess we could pass in fxns "groupPreference" and "allVotersprefer...")
        */
    
}

pred independenceOfIrrelevantAlternativesSM {
    /*
    If every voter's preference between X and Y remains unchanged,
    then the group's preference between X and Y will also remain unchanged
    (even if voters' preferences between other pairs like X and Z, Y and Z, or Z and W change).
    For simple majority, voters only have one preference. So, their preferences never change.
    */

    /* Some candidates A B C
       if A is the winner and B is a loser and C is a loser
       there should be no way to remove either B or C s.t. A does not win

       For all candidate pairs (X Y)
       We want it to be true that no candidate Z could come along s.t. 
       voter preferences between X and Y remain the same but group 
       preferences between X and Y change
       In a simple majority, this looks like the winner changing
       because that is the only scenario where group preferences are
       expressed
    */

    

    /*
        Idea... model hidden preferences? 
        For Simple Majority
        If there exist candidates A and B
        then there should be no way for a Candidate C to come along s.t. 
        the voter's preference between A and B remain the same, 
        but the group's preferences between A and B change
        Can easily see how this can happen if 
    */
}

// run {
//     wellformed
//     some c : Candidate | isSimpleMajorityWinner[c] and Election.winner = c 
//     not universalitySM
// } for exactly 3 Candidate


test expect {
    universality_holds_sm: {
        {wellformed and thereIsAWinner} implies universalitySM
    } for exactly 3 Candidate is theorem
}

// run {
//     wellformed 
//     some c : Candidate | isSimpleMajorityWinner[c] and Election.winner = c 
// }


