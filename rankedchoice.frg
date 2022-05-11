#lang forge
open "arrows.frg"

sig RankedChoiceVoter extends Voter {
    secondChoice: one Candidate,
    thirdChoice: one Candidate,

    // When examining the possibility of dictators, a 
    // hypothetical election is run in an alternate universe where
    // these represent the voter's choices
    altFirstChoice: one Candidate,
    altSecondChoice: one Candidate,
    altThirdChoice: one Candidate

}

one sig EliminatedCandidates {
    firstRound: one Candidate,
    secondRound: one Candidate,

    // When running the alternate universe elections, these are the alt elimianted candidate predicates
    altFirstRound: one Candidate,
    altSecondRound: one Candidate
}

pred wellformed {
    #Candidate >= 3
    #RankedChoiceVoter > #Candidate
    all v: Voter | v in RankedChoiceVoter
    Election.election_voters = Voter
    all v: Voter | {
        not v.firstChoice = v.secondChoice
        not v.firstChoice = v.thirdChoice
        not v.secondChoice = v.thirdChoice
    }
    
}


pred isRankedChoiceWinner[c: Candidate] {
    // The candidate either wins any of the rounds
    isFirstChoiceWinner[c] or
    isSecondChoiceWinner[c] or
    isThirdChoiceWinner[c]
    /* 
    NOTE: within the winner predicates we enforce that there was no winner for the previous round.
    Even if candidate would technically win third round with a certain elimination procedure, thirdChoiceWinner
    will return false if someone else wins first/second round.
    */
}

pred isAltRankedChoiceWinner[c: Candidate] {
    isAltFirstChoiceWinner[c] or
    isAltSecondChoiceWinner[c] or
    isAltThirdChoiceWinner[c]
}

// Number of votes to beat (must get more votes than this to have a MAJORITY)
fun NUM_VOTES_TO_BEAT: one Int {
    divide[#{v: Voter|v in Voter}, 2]
}

// Has a candidate been eliminated in the first round
pred isEliminatedFirstRound[c: Candidate] {
    EliminatedCandidates.firstRound = c
}
// Same as isEliminatedFirstRound using alternate universe voter choices
pred isEliminatedAltFirstRound[c: Candidate] {
    EliminatedCandidates.altFirstRound = c
}

// Has a candidate been eliminated in either the first or second round
pred isEliminatedFirstOrSecondRound[c: Candidate] {
    (EliminatedCandidates.firstRound = c) or 
    (EliminatedCandidates.secondRound = c)
}
// Same as isEliminatedFirstOrSecondRound using alternate universe voter choices
pred isEliminatedAltFirstOrSecondRound[c: Candidate] {
    (EliminatedCandidates.altFirstRound = c) or 
    (EliminatedCandidates.altSecondRound = c)
}


/*
 * How many votes did the candidate receieve in the first round?
 * 
 * NOTE: When calculating number of votes for a candidate, 
 * we assume that the candidate passed in has NOT been elimnated
*/
fun numFirstRoundVotes[c: Candidate]: one Int {
    #{v: Voter | v.firstChoice = c}
}
// same as numFirstRoundVotes using the alternate universe voter choices
fun numAltFirstRoundVotes[c: Candidate]: one Int {
    #{v: Voter | v.altFirstChoice = c}
}

/*
 * How many votes did the candidate receieve in the second round?
 * Considers additional votes from voters whose firstChoice was eliminated in previous round.
 * 
 * NOTE: When calculating number of votes for a candidate, 
 * we assume that the candidate passed in has NOT been elimnated
*/
fun numSecondRoundVotes[c: Candidate]: one Int {
    #{v : Voter | v.firstChoice = c or (isEliminatedFirstRound[v.firstChoice] and v.secondChoice = c)}
}
// same as numSecondRoundVotes using the alternate universe voter choices
fun numAltSecondRoundVotes[c: Candidate]: one Int {
    #{v : Voter | v.altFirstChoice = c or (isEliminatedAltFirstRound[v.altFirstChoice] and v.altSecondChoice = c)}
}

/*
 * How many votes did the candidate receieve in the third round?
 * Considers additional votes from voters whose firstChoice and secondChoice were eliminated in previous rounds.
 * 
 * NOTE: When calculating number of votes for a candidate, 
 * we assume that the candidate passed in has NOT been elimnated
*/
fun numThirdRoundVotes[c: Candidate]: one Int {
    #{v : Voter | 
        (v.firstChoice = c or 
        (isEliminatedFirstOrSecondRound[v.firstChoice] and v.secondChoice = c) or
        (isEliminatedFirstOrSecondRound[v.firstChoice] and isEliminatedFirstOrSecondRound[v.secondChoice] and v.thirdChoice = c)
        )}
}
// same as numThirdRoundVotes using the alternate universe voter choices
fun numAltThirdRoundVotes[c: Candidate]: one Int {
    #{v : Voter | 
        (v.altFirstChoice = c or 
        (isEliminatedAltFirstOrSecondRound[v.altFirstChoice] and v.altSecondChoice = c) or
        (isEliminatedAltFirstOrSecondRound[v.altFirstChoice] and isEliminatedAltFirstOrSecondRound[v.altSecondChoice] and v.altThirdChoice = c)
        )}
} 

/* Determines the candidate that would be eliminated in the first round 
 *
 * NOTE: (not necessarily used, but sets it anyway). Even if someone wins first round, sig still gets set
*/
pred candidateEliminatedFirstRound {
    // If there is a tie, a random candidate (model abstraction) of the worst performing candidates is considered eliminated
    some c: Candidate | {
        all other_c: Candidate | other_c != c implies {
            numFirstRoundVotes[c] <= numFirstRoundVotes[other_c]
        }
        EliminatedCandidates.firstRound = c
    }
}
// same as candidateEliminatedFirstRound using alternate universe voter choices
pred candidateEliminatedAltFirstRound {
    // If there is a tie, a random candidate (model abstraction) of the worst performing candidates is considered eliminated
    some c: Candidate | {
        all other_c: Candidate | other_c != c implies {
            numAltFirstRoundVotes[c] <= numAltFirstRoundVotes[other_c]
        }
        EliminatedCandidates.altFirstRound = c
    }
}

/* Determines the candidate that would be eliminated in the second round 
 *
 * NOTE: (not necessarily used, but sets it anyway). Even if someone wins first round, sig still gets set
*/
pred candidateEliminatedSecondRound {
    // If there is a tie, a random candidate (model abstraction) of the worst performing candidates is considered eliminated
    some c: Candidate | {
        // If candidate was already eliminated in the first round we can't eliminate them again
        (not isEliminatedFirstRound[c])

        all other_c: Candidate | ((not isEliminatedFirstRound[other_c]) and other_c != c) implies {
            numSecondRoundVotes[c] <= numSecondRoundVotes[other_c]
        }
        EliminatedCandidates.secondRound = c
    }
}
// same as candidateEliminatedSecondRound using alternate universe voter choices
pred candidateEliminatedAltSecondRound {
    // If there is a tie, a random candidate (model abstraction) of the worst performing candidates is considered eliminated
    some c: Candidate | {
        // If candidate was already eliminated in the first round we can't eliminate them again
        (not isEliminatedAltFirstRound[c])

        all other_c: Candidate | ((not isEliminatedAltFirstRound[other_c]) and other_c != c) implies {
            numAltSecondRoundVotes[c] <= numAltSecondRoundVotes[other_c]
        }
        EliminatedCandidates.altSecondRound = c
    }
}

// Ensures that elimination occurs properly at each step (wellformed-esque predicate, SHOULD BE CALLED IN RUN)
pred eliminationProcedure {
    candidateEliminatedFirstRound
    candidateEliminatedSecondRound

    // Handles alternate universe cases as well
    candidateEliminatedAltFirstRound
    candidateEliminatedAltSecondRound
}


// Has a given candidate won the first round?
pred isFirstChoiceWinner[c: Candidate] {
    // Candidate should get more than 50% of the votes
    numFirstRoundVotes[c] > NUM_VOTES_TO_BEAT
}
// same as isFirstChoiceWinner using alternate universe voter choices
pred isAltFirstChoiceWinner[c: Candidate] {
    numAltFirstRoundVotes[c] > NUM_VOTES_TO_BEAT
}

// There are no candidates that have won the first runoff
pred noFirstChoiceWinner{ 
    // (For 7 candidates, no one got >=4 firstChoice votes)
    no c: Candidate | {
        isFirstChoiceWinner[c]
    }
}
// same as noFirstChoiceWinner using alternate universe voter choices
pred noAltFirstChoiceWinner {
    no c: Candidate | {
        isAltFirstChoiceWinner[c]
    }
}

// Has a given candidate won the second round?
pred isSecondChoiceWinner[c: Candidate] {
    // Candidate can only win as a secondChoiceWinner if there were no first choice winners
    noFirstChoiceWinner
    // Can't have been eliminated (otherwise can't win)
    not isEliminatedFirstRound[c]
    
    numSecondRoundVotes[c] > NUM_VOTES_TO_BEAT
}
// same as isSecondChoiceWinner using alternate universe voter choices
pred isAltSecondChoiceWinner[c: Candidate] {
    // Candidate can only win as a secondChoiceWinner if there were no first choice winners
    noAltFirstChoiceWinner
    // Can't have been eliminated (otherwise can't win)
    not isEliminatedAltFirstRound[c]
    
    numAltSecondRoundVotes[c] > NUM_VOTES_TO_BEAT
}

// There are no candidates that have won the first runoff
pred noSecondChoiceWinner{ // (For 7 candidates, no one got >=4 firstChoice votes)
    no c: Candidate | {
        isSecondChoiceWinner[c]
    }
}
// same as noSecondChoiceWinner using alternate universe voter choices
pred noAltSecondChoiceWinner {
    no c: Candidate | {
        isAltSecondChoiceWinner[c]
    }
}

pred isThirdChoiceWinner[c: Candidate] {
    // Candidate can only win as a thirdChoiceWinner if there were no second choice winners
    noSecondChoiceWinner

    // Can't have been eliminated (otherwise can't win)
    not isEliminatedFirstOrSecondRound[c]

    numThirdRoundVotes[c] > NUM_VOTES_TO_BEAT
}
// same as isThirdChoiceWinner using alternate universe voter choices
pred isAltThirdChoiceWinner[c: Candidate] {
    // Candidate can only win as a thirdChoiceWinner if there were no second choice winners
    noAltSecondChoiceWinner

    // Can't have been eliminated (otherwise can't win)
    not isEliminatedAltFirstOrSecondRound[c]

    numAltThirdRoundVotes[c] > NUM_VOTES_TO_BEAT
}


// same as thereIsAWinner using alternate universe voter choices
pred thereIsAnAltWinner {
    some c: Candidate | {
        isAltRankedChoiceWinner[c]
        Election.altWinner = c
    }
}

pred thereIsAWinner {
    some c: Candidate | {
        isRankedChoiceWinner[c]
        Election.winner = c
    }

    // Run thereIsAnAltWinner required when running noDictators
    thereIsAnAltWinner
}

fun getRankedChoiceWinner[e: Election]: one Candidate {
    e.winner
}

// no single voter possesses the power to always determine the group's preference.
// ref. : https://en.wikipedia.org/wiki/Arrow%27s_impossibility_theorem
pred noDictatorsRC {
    // all v : Voter | {
    //      changeFirstPref[v] does not change winner and
    //      changeSecondPref[v] does not change winner and
    //      changeThirdPref[v] does not change winner
    // }
    no potentialDictator: Voter | {

        all other_voter: Voter | other_voter!=potentialDictator implies {
                other_voter.firstChoice = other_voter.altFirstChoice
                other_voter.secondChoice = other_voter.altSecondChoice
                other_voter.thirdChoice = other_voter.altThirdChoice
        }
        potentialDictator.firstChoice != potentialDictator.altFirstChoice
        potentialDictator.secondChoice != potentialDictator.altSecondChoice
        potentialDictator.thirdChoice != potentialDictator.altThirdChoice

        // NOTE: We just care if the election result *CHANGES*, not necessarily that the dictator gets their preferred candidate either way
        some winner: Candidate | {
            isRankedChoiceWinner[winner]
            not isAltRankedChoiceWinner[winner]
        }
    }
}

pred rcHasPrefForA[a: Candidate, b: Candidate, v: Voter] {
    (v.firstChoice = a and v.secondChoice = b) or 
    (v.firstChoice = a and v.thirdChoice = b) or
    (v.secondChoice = a and v.thirdChoice = b)
}

pred rcAllVotersPreferAtoB[a: Candidate, b: Candidate, voterSet: set Voter] {
    all v: Voter | v in voterSet implies {
        rcHasPrefForA[a, b, v]
    }
}

pred rcGroupPreference[a: Candidate, b: Candidate, voterSet: set Voter] {
    // Somehow need to add up ranked preferences
    // # of voters who prefer a to b where a is first and b second and
    // # of voters who prefer a to b where a is first and b is third and
    // # of voters who prefer a to b where a is second and b is third

    //there is a group preference for candidate A iff...
    //voters who have A as first choice + voters who have A as second and A as third
    //is greater than
    //voters who have B as first choice + voters who have B as second and A as third
    {
    add[#{vot : Voter | vot in voterSet and vot.firstChoice = a},
        #{vot : Voter | vot in voterSet and vot.secondChoice = a and vot.thirdChoice = b}]
     >
    add[#{vot : Voter | vot in voterSet and vot.firstChoice = b},
        #{vot : Voter | vot in voterSet and vot.secondChoice = b and vot.thirdChoice = a}]
    }
}

// if every voter prefers alternative X over alternative Y, then the group prefers X over Y
// ref. : https://en.wikipedia.org/wiki/Arrow%27s_impossibility_theorem
pred universalityRC {
    all disj a, b: Candidate | rcAllVotersPreferAtoB[a, b, Voter] implies rcGroupPreference[a, b, Voter]
}

// if every voter's preference between X and Y remains unchanged, 
// then the group's preference between X and Y will also remain unchanged
// ref. : https://en.wikipedia.org/wiki/Arrow%27s_impossibility_theorem
pred independenceOfIrrelevantAlternativesRC {
    not { 
        // If A is the first round winner and C is excluded, then B shouldn't end up with more votes than A
        (some disj a, b, c : Candidate | {
            isFirstChoiceWinner[a]
            {add[#{v : Voter | (v.firstChoice = c and v.secondChoice = b)}, numFirstRoundVotes[b]] > numFirstRoundVotes[a]}
        }) or
        // If A is the second round winner and C is excluded, then B shouldn't end up with enough votes to win round 1 or 2
        // TODO: Fill in how to check that B would have enough to win round 2
        (some disj a, b, c: Candidate | {
            isSecondChoiceWinner[a]
            ({add[#{v: Voter | (v.firstChoice = c and v.secondChoice = b)}, numFirstRoundVotes[b]] > NUM_VOTES_TO_BEAT})
        }) or
        // If A is the third round winner and C is excluded, then B shouldn't end up with enough votes to win round 1, 2, or 3
        // TODO: Fill in how to check that B would have enough to win round 2 or round 3
        (some disj a, b, c: Candidate | {
            isThirdChoiceWinner[a]
            {add[#{v: Voter | (v.firstChoice = c and v.secondChoice = b)}, numFirstRoundVotes[b]] > NUM_VOTES_TO_BEAT}
        })
    }
}

/* Run statements to prove that passing functions as arguments is working */
run { 
    //should run fine
    wellformed
    thereIsAWinner
    universality[rcAllVotersPreferAtoB, rcGroupPreference]
}

run { 
    //should produce unsat
    wellformed
    thereIsAWinner
    not universality[rcAllVotersPreferAtoB, rcGroupPreference]
}


run {
    wellformed
    eliminationProcedure
    thereIsAWinner

    // TODO: write testExpects
    noFirstChoiceWinner
    not noAltFirstChoiceWinner

    not noDictatorsRC


} for exactly 3 Candidate, exactly 7 Voter

test expect {
    vacuity_rc: {
        wellformed
    } is sat

    canGetWinner: {
        wellformed
        eliminationProcedure
        thereIsAWinner
    } is sat

    universality_holds_rc: {
        {wellformed and thereIsAWinner} implies universalityRC
    } for exactly 3 Candidate is theorem

    // There are counterexamples where IIA fails for ranked choice voting
    independence_of_irrelevant_alternatives_rc_fails: {
        wellformed
        eliminationProcedure
        thereIsAWinner
        not independenceOfIrrelevantAlternativesRC
    } for exactly 3 Candidate, exactly 7 Voter is sat

    // There are also instances where IIA is upheld for ranked choice voting
    independence_of_irrelevant_alternatives_rc: {
        wellformed
        eliminationProcedure
        thereIsAWinner
        independenceOfIrrelevantAlternativesRC
    } for exactly 3 Candidate, exactly 7 Voter is sat
}

// Run to see examples of a ranked choice vote
// run {
//     wellformed
//     eliminationProcedure
//     thereIsAWinner
//     // Below 2 lines force interesting examples of RCV
//     noFirstChoiceWinner
//     noSecondChoiceWinner // YIELDS Unsat with 3 candidate (presumably impossible to not have a winner after second round w/ 3 candidates and 7 voters)
// } for exactly 4 Candidate, exactly 7 Voter

// Run to see examples of ranked choice voting failing at IIA
// Tested with exactly 4 Candidate, exactly 7 Voter
// and with exactly 3 Candidate, exactly 7 Voter
run {
    wellformed
    eliminationProcedure
    thereIsAWinner

    not noDictatorsRC

    not independenceOfIrrelevantAlternativesRC
} for exactly 3 Candidate, exactly 7 Voter
