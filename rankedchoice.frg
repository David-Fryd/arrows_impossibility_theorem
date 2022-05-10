#lang forge
open "arrows.frg"

sig RankedChoiceVoter extends Voter {
    secondChoice: one Candidate,
    thirdChoice: one Candidate
}

one sig EliminatedCandidates {
    firstRound: one Candidate,
    secondRound: one Candidate
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

// TODO: Figure out candidate elimination and using second/third preference
//       of voters whose more preferred candidate is eliminated
//       Maybe keep track of eliminated candidates in Election sig?
pred isRankedChoiceWinner[c: Candidate] {
    // The candidate either wins via first choice votes
    isFirstChoiceWinner[c] or
    isSecondChoiceWinner[c] or
    isThirdChoiceWinner[c]
    
    
     //or
    // Or the candidate wins via second choice votes
    // (not isFirstChoiceWinner[c] and isSecondChoiceWinner[c]) or
    // // Or the candidate wins via third choice votes
    // ((not isFirstChoiceWinner[c] and not isSecondChoiceWinner[c]) and isThirdChoiceWinner[c])
}


fun NUM_VOTES_TO_BEAT: one Int {
    divide[#{v: Voter|v in Voter}, 2]
}

// Has a candidate been eliminated in the first round
pred isEliminatedFirstRound[c: Candidate] {
    EliminatedCandidates.firstRound = c
}

// Has a candidate been eliminated in either the first or second round
pred isEliminatedFirstOrSecondRound[c: Candidate] {
    (EliminatedCandidates.firstRound = c) or 
    (EliminatedCandidates.secondRound = c)
}

// When calculating number of votes for a candidate, we assume that the candidate passed in has NOT been elimnated
fun numFirstRoundVotes[c: Candidate]: one Int {
    #{v: Voter | v.firstChoice = c}
}

// When calculating number of votes for a candidate, we assume that the candidate passed in has NOT been elimnated
fun numSecondRoundVotes[c: Candidate]: one Int {
    // For voters who had an eliminated candidate as their first choice,
    // use their second choice. Otherwise, use first choice
    #{v : Voter | v.firstChoice = c or (isEliminatedFirstRound[v.firstChoice] and v.secondChoice = c)}
}

// When calculating number of votes for a candidate, we assume that the candidate passed in has NOT been elimnated
fun numThirdRoundVotes[c: Candidate]: one Int {
    //TODO: Need to add in one more that counts them as secondChoice as well
    #{v : Voter | 
        (v.firstChoice = c or 
        (isEliminatedFirstOrSecondRound[v.firstChoice] and v.secondChoice = c) or
        (isEliminatedFirstOrSecondRound[v.firstChoice] and isEliminatedFirstOrSecondRound[v.secondChoice] and v.thirdChoice = c)
        )}
}

// // Returns true if this is the candidate that receieved the least amount of votes during firstChoice round
// pred eliminatedInFirstRound[c: Candidate] {
//     // All other candidates have more votes than this candidate (if equal, other candidate could also be eliminated)
//     all other_c: Candidate | other_c != c implies {
//         numFirstRoundVotes[c] <= numFirstRoundVotes[other_c]
//     }
// }

// Determines the candidate that would be eliminated in the first round (not necessarily used, but sets it anyway)
pred candidateEliminatedFirstRound {
    // If there is a tie, a random candidate (model abstraction) of the worst performing candidates is considered eliminated
    some c: Candidate | {
        all other_c: Candidate | other_c != c implies {
            numFirstRoundVotes[c] <= numFirstRoundVotes[other_c]
        }
        EliminatedCandidates.firstRound = c
    }
}

// Determines the candidate that would be eliminated in the second round (not necessarily used, but sets it anyway)
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

// Ensures that elimination occurs properly at each step
pred eliminationProcedure {
    candidateEliminatedFirstRound
    candidateEliminatedSecondRound
}


// Has a given candidate won during first Round
pred isFirstChoiceWinner[c: Candidate] {
    // Candidate should get more than 50% of the votes
    numFirstRoundVotes[c] > NUM_VOTES_TO_BEAT
}

// There are no candidates that have won the first runoff
pred noFirstChoiceWinner{ // (For 7 candidates, no one got >=4 firstChoice votes)
    no c: Candidate | {
        isFirstChoiceWinner[c]
    }
}

pred isSecondChoiceWinner[c: Candidate] {
    // Candidate can only win as a secondChoiceWinner if there were no first choice winners
    noFirstChoiceWinner
    // Can't have been eliminated (otherwise can't win)
    not isEliminatedFirstRound[c]
    
    // For voters who had an eliminated candidate as their first choice,
    // use their second choice. Otherwise, use first choice
    numSecondRoundVotes[c] > NUM_VOTES_TO_BEAT
}

// There are no candidates that have won the first runoff
pred noSecondChoiceWinner{ // (For 7 candidates, no one got >=4 firstChoice votes)
    no c: Candidate | {
        isSecondChoiceWinner[c]
    }
}

pred isThirdChoiceWinner[c: Candidate] {
    // Candidate can only win as a thirdChoiceWinner if there were no second choice winners
    noSecondChoiceWinner

    // Can't have been eliminated (otherwise can't win)
    not isEliminatedFirstOrSecondRound[c]

    // For voters who had an eliminated candidate as their first choice,
    // use their second choice. Otherwise, use first choice
    numThirdRoundVotes[c] > NUM_VOTES_TO_BEAT
}


// pred isThirdChoiceWinner[c: Candidate] {
//     #{v : Voter | v.firstChoice = c or (isEliminated[v.firstChoice] and isEliminated[v.secondChoice] and v.thirdChoice = c)} > divide[#{v: Voter|v in Voter}, 2]
// }

// pred isEliminated[c: Candidate] {
//     // Assuming we store eliminated candidates in Election sig
//     // c in Election.eliminatedCandidates
//     1>0
// }

pred thereIsAWinner {
    some c: Candidate | {
        isRankedChoiceWinner[c]
        Election.winner = c
    }
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
    // TODO: Fill in
}


run {
    wellformed
    eliminationProcedure
    thereIsAWinner
    

    // Below 2 lines force interesting examples of RCV
    noFirstChoiceWinner
    noSecondChoiceWinner // YIELDS Unsat with 3 candidate (presumably impossible to not have a winner after second round w/ 3 candidates and 7 voters)

} for exactly 4 Candidate, exactly 7 Voter