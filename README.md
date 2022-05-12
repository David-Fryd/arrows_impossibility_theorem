# Arrow's Impossibility Theorem Applied to Simple Plurality and Ranked Choice Voting Systems

Arrow’s Impossibility Theorem demonstrates that no voting system exists such that these three properties hold with more than 2 candidates:
- **Universality**: If everyone in the group prefers candidate A to candidate B then the social ranking prefers A to B
- **Independence of Irrelevant Alternatives:** If everyone's preference between A and B remains unchanged, then the group's preference will also remain unchanged, regardless of the addition of other candidates (like C, D, E, etc).
- **No Dictators:** There are no dictators. No one voter can decide the outcome for the entire group.

Voting systems may hold some combination of these properties, but not all three simultaneously.   


We chose to examine and apply Arrow's Impossibility Theorem to a simple plurality voting system, and a ranked choice voting system. We examined and affirmed the following conclusions:

**Conclusions**:
- **Universality**: Both a simple plurality voting system and ranked choice voting system always respect the principle of Universality.
- **Independence of Irrelevant Alternatives (IIA)**: The principle of IIA is *not always true (not theorem)* for both simple pluraility and ranked choice voting systems. i.e. there are cases which respect this principle, and other cases that do not.
- **No Dictators:**: The principle of No Dictators is *not always true (not theorem)* for both simple pluraility and ranked choice voting systems. i.e. there are cases which respect this principle, and other cases that do not.


## Challenges/Obstacles
- Abstracting Arrow's predicates to apply to a generic voting system:
  - Ideally we wanted to write three predicates representing the three predicates of Arrow's impossibility theorem, and apply those same predicates to any voting system. 
  - Since the voting systems are modeled differently, the exact logic which satisfies a particular one of Arrow's predicates is also different. A solution to this is to define generic predicates and pass functions with similar purpose as lambdas, where the passed functions are defined specifically for each voting system. 
    - We were able to demonstrate that this approach works with the *Universality principle*. Because the Universality predicate was the most similar between the two voting systems, it was easiest to implement generically. Due to time constraints combined with other design/modeling challenges, we were unable to generically implement the other two Arrow's predicates, however it is technically feasible. 
- Alternate Universes/Secret Preferences
  - Some of Arrow's predicates involve "what-if" assertions, inviting a comparison of two different versions of the same election. "No Dictators" states that *if* one person were to vote differently, they shouldn't be able to change the outcome of the election. Practically this means we have to simulate two similar parallel elections with mostly common factors.
  - The original models of our voting systems (SP & RCV) simulate a single instance of the election, which does not provide enough information to analyze Arrow's predicates. Although we could manually run the model twice over two manually changed set of constraints, there is no easy way to feed the results of two separate instances into Forge predicates.
    - In order to address this issue, we decided to simulate "alternate" versions of elections simultaneously with the main election instance by creating analogous fields and predicates. i.e. for Ranked Choice Voting, not only do voters have a `firstChoice`, `secondChoie`, and `thirdChoice`, but they also have an `altFirstChoice`, `altSecondChoie`, and `altThirdChoice`. We also have predicates that determine the winner of the actual election, and a predicate that determines the winner of the alternate election. We can therefore constrain certain voters to act the same/differently between two instances of an election and directly access/compare the circumstances of both elections.
    - These analogous predicates/fields behave very similarly. Even though the logic is the same and the code is very similar, because we can't pass fields as arguments to preds/functions, we could not make a generic version of `isWinnerOfElection`, and had to make two very similar predicates that use different fields/sigs.
- Non-temporal handling of runoff cases in forge
  - Ranked Choice Voting (RCV) involves an instant run-off system which was non-trivial to simulate. If there is not a candidate that has won after the first round of voting is complete, the candidate with the least amount of votes is eliminated and the election is run again, where if a voter's `firstChoice` was the eliminated candidate, their `secondChoice` is considered. Similar logic is applied to the third round of voting, except as each round progresses the processes for determining the correct choice to count grows slightly more complex.
  - If we were just modeling a ranked choice voting system, a natural choice might be to approach the problem *temporally*, where states of the election correspond to the rounds of instant run-off voting. Because we are mainly interested in the final outcome of elections and other voting systems were non-temporal, we decided to approach modeling RCV from a non-temporal standpoint. 
  - We were able to devise a method that properly modeled a full instance of RCV, however it required us to explicitly define and connect the steps of instant run-off voting.
    - Because the run-off procedures had to be explicitly defined at each step, we chose to simplify the model and only consider a 3-choice RCV system. This allows us to produce interesting results and make general assertions about RCV while not overcomplicating the model.


### **Abstractions/Choices**

- All Voters vote in the election. We do not consider people who abstain/don't vote in our model because practically they are not "voters" in the election. We restrict ourselves to analyzing voters because they are the logically relevant components to voting systems, particularly when it comes to Arrow's impossibility theorem.

#### *Simple Plurality (SP)*
- For Simple Plurality we abstract out the cases where there are ties (we enforce that *some candidate* has the most amount of votes and therefore wins). 
  - We do this because we are only interested in the cases where elections can be *won* by two *distinct* candidates in response to a single violation of one of *Arrow's Fairness Principles* (not the cases where there is a winner/tie in response to a violation).
  - Importantly, we note that there are external mechanisms not native to a **Simple Plurality** voting system that handle the situation in case of a tie. (Usually, another round of voting is held, or some other system is invoked in the case of a tie). Because of this, we assume for the sake of simplicity and consistency that there is a winner after a single round of **Simple Plurality** voting.

#### *Ranked Choice Voting (RCV)*
(TODO: go through preds and use comments i wrote to inform the things discussed here)
- Ties in rounds are randomly solved (model abstraction)
  - If two candidates receieve an equally low amount of votes in a round, a non-deterministic candidate among those with the least votes is eliminated. There is no established way that a generic RCV system handles ties among losing candidates, mostly because with a large amount of voters this is extremely rare. Nonetheless, this seemed like the least complex/fair choice to model.
- We enforce that there is a candidate for each choice (one, not lone). Following the spirit of our "All voters vote" design decision,
  - It is true that some RCV systems offer more choices than a voter must choose, but for the sake of modeling an ideal-RCV election (and making assertions about the ideal system) combined with Forge model challenges, we chose to enforce that all Voters provide a candidate for each possible choice.
- Each voter has exactly 3 choices to rank
  - While in many RCV systems, the number of choices you could enter is theoretically limited by the number of candidates of an election, challenges with modeling RCV in Forge lead us to choose 3 choices as a happy medium. (See our section re: Challenges/Obstacles)
- A lot of the abstraction/simplification choices made for RCV were a direct response to challenging Forge limitations combined with how we decided to model RCV non-temporally.
