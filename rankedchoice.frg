#lang forge
open "arrows.frg"

sig RankedChoiceVoter extends Voter {}

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
    // Or the candidate wins via second choice votes
    (not isFirstChoiceWinner[c] implies isSecondChoiceWinner[c]) or
    // Or the candidate wins via third choice votes
    ((not isFirstChoiceWinner[c] and not isSecondChoiceWinner[c]) implies isThirdChoiceWinner[c])
}

pred isFirstChoiceWinner[c: Candidate] {
    // Candidate should get more than 50% of the votes
    #{v: Voter | v.firstChoice = c} > divide[#{v: Voter}, 2]
}

pred isSecondChoiceWinner[c: Candidate] {
    // For voters who had an eliminated candidate as their first choice,
    // use their second choice. Otherwise, use first choice
    #{v : Voter | v.firstChoice = c or (isEliminated[v.firstChoice] and v.secondChoice = c)} > divide[#{v: Voter}, 2]
}

pred isThirdChoiceWinner[c: Candidate] {
    #{v : Voter | v.firstchoice = c or (isEliminated[v.firstChoice] and isEliminated[v.secondChoice] and v.thirdChoice = c)} > divide[#{v: Voter}, 2]
}

pred isEliminated[c: Candidate] {
    // Assuming we store eliminated candidates in Election sig
    c in Election.eliminatedCandidates
}

pred thereIsAWinner {
    some c: Candidate | isRankedChoiceWinner[c] and Election.winner = c
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

pred rcAllVotersPreferAtoB[a: Candidate, b: Candidate, voterSet set Voter] {
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
