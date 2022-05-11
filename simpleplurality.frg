#lang forge
open "arrows.frg"


//may add hidden preferences to 
sig SimplePluralityVoter extends Voter {
    // If you eliminated their first choice, they would vote for this candidate
   secretPreference: one Candidate
}


/*
    Anticipate issues with Election.election_voters/any set of voters/choices of voters changing between calls? 
*/
pred wellformed {
    #Candidate = 3
    #SimplePluralityVoter > #Candidate
    all v : Voter | v in SimplePluralityVoter
    Election.election_voters = Voter
    // TODO: Does this have to be true? 
    // all v : Voter | (v.firstChoice != v.secretPreference)
}

/* enforces that the winner of the election has the most votes */
pred isSimplePluralityWinner[c : Candidate] { //todo: take in a set of simpleplurality voters
    all other_c : Candidate | other_c != c implies {
        #{sv : SimplePluralityVoter | sv.firstChoice = c} > #{sv : SimplePluralityVoter | sv.firstChoice = other_c}
    }
}

/* enforces that the winner of the election has the most votes using people's secret preferences */
pred isSimplePluralityWinnerSecretPref[c : Candidate] { //todo: take in a set of simpleplurality voters
    all other_c : Candidate | other_c != c implies {
        #{sv : SimplePluralityVoter | sv.secretPreference = c} > #{sv : SimplePluralityVoter | sv.secretPreference = other_c}
    }
}


// TODO: Replace the original [isSimplePluralityWinner] eventually
pred isSimplePluralityWinnerAbstractVersion[c : Candidate] { //todo: take in a set of simpleplurality voters
    all other_c : Candidate | other_c != c implies {
        #{sv : SimplePluralityVoter | sv.firstChoice = c} > #{sv : SimplePluralityVoter | sv.firstChoice = other_c}
    }
}

pred thereIsAWinner {
    some c : Candidate | isSimplePluralityWinner[c] and Election.winner = c
}

//TODO: rename this getSimplePluralityWinner?
fun mostFirstChoiceVotes[e : Election]: one Candidate {
    e.winner
}

// We simulate 2 parallel elections where other voters choices in both elections (firstChoice & secretPref represent)
pred noDictatorsSP { 
    //no Voter | firstChoice changing changes outcome
    //no way for there to be an even number of votes assigned to two candidates, and then 1 more vote cast
    // isSimplePluralityWinnerAbstractVersion doesnt change when a single person's first choice changes
    
    no potentialDictator: Voter | {

        all other_voter: Voter | other_voter!=potentialDictator implies {
                other_voter.firstChoice = other_voter.secretPreference
        }
        potentialDictator.firstChoice != potentialDictator.secretPreference

        // NOTE: We just care if the election result *CHANGES*, not necessarily that the dictator gets their preferred candidate either way
        some winner: Candidate | {
            isSimplePluralityWinner[winner]
            not isSimplePluralityWinnerSecretPref[winner]
        }
    }
}


pred spHasPrefForA[a : Candidate, b : Candidate, v : Voter] {
    v.firstChoice = a
}

pred spAllVotersPreferAtoB[a : Candidate, b : Candidate, voterSet: set Voter] {
    all v: Voter | v in voterSet implies {
        spHasPrefForA[a,b,v]
    }
}

pred spGroupPreference[a : Candidate, b : Candidate, voterSet: set Voter] {
    #{vot : Voter | vot in voterSet and vot.firstChoice = a} > #{vot : Voter | vot in voterSet and vot.firstChoice = b}
}

//Universality predicate specific to Simple Plurality
pred universalitySP { 
    // For simple plurality, its a bit tautologic, but thats what impossibility translates to here
    //if everyone prefers A to B, then the group prefers A to B
    all disj a,b : Candidate | spAllVotersPreferAtoB[a, b, Voter] implies spGroupPreference[a, b, Voter]
        //#{v : Voter | v.firstChoice = a} > #{v : Voter | v.firstChoice = b}
        /**
        groupPreference[a,b,V] implies allVoterspreferAtoB[a,b,V] ?
        (i guess we could pass in fxns "groupPreference" and "allVotersprefer...")
        */
    
}

pred independenceOfIrrelevantAlternativesSP {
    /* Here we model hidden preferences s.t. 
        If there exist candidates A and B
        then there should be no way for a Candidate C to come along s.t. 
        the voter's preference between A and B remain the same, 
        but the group's preferences between A and B change
        
        in other words, if we remove candidate C, does B now win over A? 
    */

    // Guard condition
    all v : Voter | (v.firstChoice != v.secretPreference)

    not { 
        some disj a, b, c : Candidate | {
            isSimplePluralityWinner[a] implies 
            {add[#{v : Voter | (v.firstChoice = c and v.secretPreference = b)}, #{v: Voter | v.firstChoice = b}] > #{v: Voter | v.firstChoice = a}}
        }
    }
    
}

// run {
//     wellformed
//     some c : Candidate | isSimplePluralityWinner[c] and Election.winner = c 
//     not universalitySP
// } for exactly 3 Candidate

//universality general
run {

}

test expect {
    vacuousTest: {
        wellformed
    } for exactly 3 Candidate, exactly 7 Voter is sat

    canGetWinner: {
        wellformed
        thereIsAWinner
    } for exactly 3 Candidate, exactly 7 Voter is sat

    universality_holds_sp: {
        {wellformed and thereIsAWinner} implies universalitySP
    } for exactly 3 Candidate, exactly 7 Voter is theorem

    //proving that IOIA is satisfiable, but not theorem
    possible_independence_of_irrelevant_alternatives_sp: {
        wellformed
        thereIsAWinner
        independenceOfIrrelevantAlternativesSP
    } for exactly 3 Candidate, exactly 7 Voter is sat

    not_independence_of_irrelevant_alternatives_sp: {
        wellformed
        thereIsAWinner
        not independenceOfIrrelevantAlternativesSP
    } for exactly 3 Candidate, exactly 7 Voter is sat

    //proving that no dictators is satisfiable, but not theorem
    no_dictators_sp: {
        wellformed
        thereIsAWinner
        noDictatorsSP
    } for exactly 3 Candidate, exactly 7 Voter is sat

    not_no_dictators_sp: {
        wellformed
        thereIsAWinner
        not noDictatorsSP
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

//     not independenceOfIrrelevantAlternativesSP
// } for exactly 3 Candidate, exactly 7 Voter





// No Dictators
run {
    wellformed
    thereIsAWinner

    not noDictatorsSP
    // noDictatorsSP //noDictatorsSP is unsat!
} for exactly 3 Candidate, exactly 7 Voter




// run {
//     wellformed
//     thereIsAWinner
//     all c : Candidate | {
//         some v : Voter | v.firstChoice = c
//     }
//     not independenceOfIrrelevantAlternativesSP
// } for exactly 3 Candidate, exactly 7 Voter


