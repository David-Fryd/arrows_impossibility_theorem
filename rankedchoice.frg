#lang forge
open "arrows.frg"

sig RankedChoiceVoter extends Voter {
    secondChoice: one Candidate,
    thirdChoice: one Candidate
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
    isFirstChoiceWinner[c] //or
    // Or the candidate wins via second choice votes
    // (not isFirstChoiceWinner[c] and isSecondChoiceWinner[c]) or
    // // Or the candidate wins via third choice votes
    // ((not isFirstChoiceWinner[c] and not isSecondChoiceWinner[c]) and isThirdChoiceWinner[c])
}


fun NUM_VOTES_TO_BEAT: one Int {
    divide[#{v: Voter|v in Voter}, 2]
}

fun numFirstRoundVotes[c: Candidate]: one Int {
    #{v: Voter | v.firstChoice = c}
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

// Returns true if this is the candidate that receieved the least amount of votes during firstChoice round
pred eliminatedInFirstRound[c: Candidate] {
    // All other candidates have more votes than this candidate (if equal to this, that candidate is ALSO eliminated)
    all other_c: Candidate | other_c != c implies {
        numFirstRoundVotes[c] <= numFirstRoundVotes[other_c]
    }
}

pred eliminatedSecondChoice[c: Candidate] {
    // For all candidates that weren't elimnated n first round
    
}

// leastAmountOfVotesAsFirstChoice replaces isEliminated TODO: David tn
pred isSecondChoiceWinner[c: Candidate] {
    // Candidate can only win as a secondChoiceWinner if there were no first choice winners
    noFirstChoiceWinner
    
    // For voters who had an eliminated candidate as their first choice,
    // use their second choice. Otherwise, use first choice
    #{v : Voter | v.firstChoice = c or (eliminatedInFirstRound[v.firstChoice] and v.secondChoice = c)} > divide[#{v: Voter|v in Voter}, 2]
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
        // isRankedChoiceWinner[c]
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
    thereIsAWinner

    noFirstChoiceWinner

} for exactly 3 Candidate, exactly 7 Voter


/*

Is winner first choice, just looks at firstChoice

iswinnerSecondChoice[c], looks at BOTH firstChoice and secondChoice and combines the two (and nO ONE was winnerFirstChoice)

*/