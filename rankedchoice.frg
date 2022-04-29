#lang forge
open "arrows.frg"

sig RankedChoiceVoter extends Voter {}

pred wellformed {
    #{Candidate} >= 3
    #{RankedChoiceVoter} > #{Candidate}
    all v: Voter | v in RankedChoiceVoter
    Election.election_voters = Voter
}

pred isRankedChoiceWinner[c: Candidate] {
    // The candidate either wins via first choice votes
    isFirstChoiceWinner[c] or
    // Or the candidate wins via second choice votes
    (not isFirstChoiceWinner[c] implies isSecondChoiceWinner[c]) or
    // Or the candidate wins via third choice votes
    ((not isFirstChoiceWinner[c] and not isSecondChoiceWinner[c]) implies isThirdChoiceWinner[c])
}

// TODO: Figure out candidate elimination and using second/third prefernce
//       of voters whose more preferred candidate is eliminated

pred thereIsAWinner {
    some c: Candidate | isRankedChoiceWinner[c] and Election.winner = c
}

fun getRankedChoiceWinner[e: Election]: one Candidate {
    e.winner
}