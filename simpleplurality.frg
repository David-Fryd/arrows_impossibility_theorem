#lang forge
open "arrows.frg"


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

/* 
    Enforces that the winner of the election has the most votes 
*/
pred isSimplePluralityWinner[c : Candidate] { //todo: take in a set of simpleplurality voters
    all other_c : Candidate | other_c != c implies {
        #{sv : SimplePluralityVoter | sv.firstChoice = c} > #{sv : SimplePluralityVoter | sv.firstChoice = other_c}
    }
}

/* 
    Enforces that the winner of the election has the most votes using people's secret preferences 
*/
pred isSimplePluralityWinnerSecretPref[c : Candidate] { //todo: take in a set of simpleplurality voters
    all other_c : Candidate | other_c != c implies {
        #{sv : SimplePluralityVoter | sv.secretPreference = c} > #{sv : SimplePluralityVoter | sv.secretPreference = other_c}
    }
}

/*
    Sets an alternative winner based on secret preferences for visualizing no dictators
*/
pred thereIsAnAlternativeWinner {
    some c : Candidate | isSimplePluralityWinnerSecretPref[c] and Election.altWinner = c
}

/*
    Sets a winner by plurality (most votes) for the election
*/
pred thereIsAWinner {
    some c : Candidate | isSimplePluralityWinner[c] and Election.winner = c
    thereIsAnAlternativeWinner
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

/* Run statements to prove that passing functions as arguments is working */
// run { 
//     //should run fine
//     wellformed
//     thereIsAWinner
//     universality[spAllVotersPreferAtoB, spGroupPreference]
// }

// run { 
//     //should produce unsat
//     wellformed
//     thereIsAWinner
//     not universality[spAllVotersPreferAtoB, spGroupPreference]
// }

// test expect {
//     vacuousTest: {
//         wellformed
//     } for exactly 3 Candidate, exactly 7 Voter is sat

//     canGetWinner: {
//         wellformed
//         thereIsAWinner
//     } for exactly 3 Candidate, exactly 7 Voter is sat

//     universality_holds_sp: {
//         {wellformed and thereIsAWinner} implies universalitySP
//     } for exactly 3 Candidate, exactly 7 Voter is theorem

//     universality_generic_holds_sp: {
//         {wellformed and thereIsAWinner} implies universality[spAllVotersPreferAtoB, spGroupPreference]
//     } for exactly 3 Candidate, exactly 7 Voter is theorem

//     //proving that IOIA is satisfiable, but not theorem
//     possible_independence_of_irrelevant_alternatives_sp: {
//         wellformed
//         thereIsAWinner
//         independenceOfIrrelevantAlternativesSP
//     } for exactly 3 Candidate, exactly 7 Voter is sat

//     not_independence_of_irrelevant_alternatives_sp: {
//         wellformed
//         thereIsAWinner
//         not independenceOfIrrelevantAlternativesSP
//     } for exactly 3 Candidate, exactly 7 Voter is sat

//     //proving that no dictators is satisfiable, but not theorem
//     no_dictators_sp: {
//         wellformed
//         thereIsAWinner
//         noDictatorsSP
//     } for exactly 3 Candidate, exactly 7 Voter is sat

//     not_no_dictators_sp: {
//         wellformed
//         thereIsAWinner
//         not noDictatorsSP
//     } for exactly 3 Candidate, exactly 7 Voter is sat
// }

/*
 Uncomment this to see an instance which violates independence of irrelevant alternatives 
 For this, the most useful visualization tool are the tables in Sterling!

 instance violating Independence of Irrelevant Alternatives 
 */

run {
    wellformed
    thereIsAWinner

    some disj a, b, winner: Candidate | {
        #{v: Voter | v.firstChoice = winner} = 6
        #{v: Voter | v.firstChoice = b} = 1
        #{v: Voter | v.firstChoice = a} = 0
    }

    //independenceOfIrrelevantAlternativesSP
} for exactly 3 Candidate, exactly 7 Voter




/*
 Uncomment this to see an instance which violates no dictators
 For this, the simple plurality visualizer will be useful to see which voter is the "dictator"

 instance violating No Dictators
 */
run {
    wellformed
    thereIsAWinner

    not noDictatorsSP
    // noDictatorsSP // uncomment this and comment out line above if you want to see a non-violating instance
} for exactly 3 Candidate, exactly 7 Voter




// run {
//     wellformed
//     thereIsAWinner
//     all c : Candidate | {
//         some v : Voter | v.firstChoice = c
//     }
//     not independenceOfIrrelevantAlternativesSP
// } for exactly 3 Candidate, exactly 7 Voter


