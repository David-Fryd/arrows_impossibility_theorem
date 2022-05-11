#lang forge
open "arrows.frg"


//may add hidden preferences to 
sig SimpleMajorityVoter extends Voter {
    // If you eliminated their first choice, they would vote for this candidate
   secretPreference: one Candidate
}


/*
    Anticipate issues with Election.election_voters/any set of voters/choices of voters changing between calls? 
*/
pred wellformed {
    #Candidate = 3
    #SimpleMajorityVoter > #Candidate
    all v : Voter | v in SimpleMajorityVoter
    Election.election_voters = Voter
    // TODO: Does this have to be true? 
    // all v : Voter | (v.firstChoice != v.secretPreference)
}

/* enforces that the winner of the election has the most votes */
pred isSimpleMajorityWinner[c : Candidate] { //todo: take in a set of simplemajority voters
    all other_c : Candidate | other_c != c implies {
        #{sv : SimpleMajorityVoter | sv.firstChoice = c} > #{sv : SimpleMajorityVoter | sv.firstChoice = other_c}
    }
}

/* enforces that the winner of the election has the most votes using people's secret preferences */
pred isSimpleMajorityWinnerSecretPref[c : Candidate] { //todo: take in a set of simplemajority voters
    all other_c : Candidate | other_c != c implies {
        #{sv : SimpleMajorityVoter | sv.secretPreference = c} > #{sv : SimpleMajorityVoter | sv.secretPreference = other_c}
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

// We simulate 2 parallel elections where other voters choices in both elections (firstChoice & secretPref represent)
pred noDictatorsSM { 
    //no Voter | firstChoice changing changes outcome
    //no way for there to be an even number of votes assigned to two candidates, and then 1 more vote cast
    // isSimpleMajorityWinnerAbstractVersion doesnt change when a single person's first choice changes
    
    no potentialDictator: Voter | {

        all other_voter: Voter | other_voter!=potentialDictator implies {
                other_voter.firstChoice = other_voter.secretPreference
        }
        potentialDictator.firstChoice != potentialDictator.secretPreference

        // NOTE: We just care if the election result *CHANGES*, not necessarily that the dictator gets their preferred candidate either way
        some winner: Candidate | {
            isSimpleMajorityWinner[winner]
            not isSimpleMajorityWinnerSecretPref[winner]
        }
    }

         
    
    // not{
    //     // NOTE: We just care if the election result *CHANGES*, not necessarily that the dictator gets their preferred candidate either way
    //     some dictator: Voter, winner: Candidate | {
    //         isSimpleMajorityWinner[winner]
    //         not isSimpleMajorityWinnerSecretPref[winner]
    //     }

    //     // isSimpleMajorityWinnerSecretPref[]
       
    //     // // dictators choice 1 and original winner of the election not necessarily disjoint
    //     // some dictator: Voter, disj winner1,winner2: Candidate | {

    //     //     all other_voter: Voter | other_voter!=dictator implies {
    //     //         other_voter.firstChoice = other_voter.secretPreference
    //     //     } 
    //     //     dictator.firstChoice != dictator.secretPreference


    //     //     (dictator.firstChoice = winner1) implies isSimpleMajorityWinner[originalWinner]
    //     //     (dictator.firstChoice = winner2) implies not isSimpleMajorityWinner[originalWinner]
    //     // }
    // }
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
        Idea... model hidden preferences? 
        For Simple Majority
        If there exist candidates A and B
        then there should be no way for a Candidate C to come along s.t. 
        the voter's preference between A and B remain the same, 
        but the group's preferences between A and B change
        Can easily see how this can happen if 
    */
    //if we remove candidate C, does B now win over A? 

    // Guard condition
    all v : Voter | (v.firstChoice != v.secretPreference)

    not { 
        some disj a, b, c : Candidate | {
            isSimpleMajorityWinner[a] implies 
            {add[#{v : Voter | (v.firstChoice = c and v.secretPreference = b)}, #{v: Voter | v.firstChoice = b}] > #{v: Voter | v.firstChoice = a}}
        }
    }
    
}

// run {
//     wellformed
//     some c : Candidate | isSimpleMajorityWinner[c] and Election.winner = c 
//     not universalitySM
// } for exactly 3 Candidate


test expect {
    vacuousTest: {
        wellformed
    } for exactly 3 Candidate, exactly 7 Voter is sat

    canGetWinner: {
        wellformed
        thereIsAWinner
    } for exactly 3 Candidate, exactly 7 Voter is sat

    universality_holds_sm: {
        {wellformed and thereIsAWinner} implies universalitySM
    } for exactly 3 Candidate, exactly 7 Voter is theorem

    independence_of_irrelevant_alternatives_sm: {
        wellformed
        thereIsAWinner
        not independenceOfIrrelevantAlternativesSM
    } for exactly 3 Candidate, exactly 7 Voter is sat

    no_dictators_sm: {
        wellformed
        thereIsAWinner
        not noDictatorsSM
    } for exactly 3 Candidate, exactly 7 Voter is sat
}

// Independence of Irrelevant Alternatives
// run {
//     wellformed
//     thereIsAWinner

//     some disj a, b, winner: Candidate | {
//         #{v: Voter | v.firstChoice = winner} = 3
//         #{v: Voter | v.firstChoice = b} = 2
//         #{v: Voter | v.firstChoice = a} = 2
//     }

//     not independenceOfIrrelevantAlternativesSM
// } for exactly 3 Candidate, exactly 7 Voter





// No Dictators
run {
    wellformed
    thereIsAWinner

    not noDictatorsSM
    // noDictatorsSM //noDictatorsSM is unsat!
} for exactly 3 Candidate, exactly 7 Voter




// run {
//     wellformed
//     thereIsAWinner
//     all c : Candidate | {
//         some v : Voter | v.firstChoice = c
//     }
//     not independenceOfIrrelevantAlternativesSM
// } for exactly 3 Candidate, exactly 7 Voter


