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


### Challenges/Obstacles
- Abstracting Arrow's predicates to apply to a generic voting system:
  - Ideally we wanted to write three predicates representing the three predicates of Arrow's impossibility theorem, and apply those same predicates to any voting system. (TODO: Discuss forge limitations, non-extensible/non-dynamic sigs, how different the voting system models were)
- Alternate Universes/Secret Preferences
  - Some of Arrow's predicates involve "what-if" assertions, inviting a comparison of two different versions of the same election. "No Dictators" states that *if* one person were to vote differently, they shouldn't be able to change the outcome of the election. Practically this means we have to ... (TODO: talk more about simultaneous)
- Non-temporal handling of runoff cases in forge
  - Ranked Choice Voting (RCV) requires a "run-off" system ... A lot of the abstraction/simplification choices made for RCV were a direct result of addressing this issue.


### **Abstractions/Choices in Voting Systems**


#### *Simple Plurality (SP)*
- For Simple Plurality we abstract out the cases where there are ties (we enforce that *some candidate* has the most amount of votes and therefore wins). 
  - We do this because we are only interested in the cases where elections can be *won* by two *distinct* candidates in response to a single violation of one of *Arrow's Fairness Principles* (not the cases where there is a winner/tie in response to a violation).
  - Importantly, we note that there are external mechanisms not native to a **Simple Majority** voting system that handle the situation in case of a tie. (Usually, another round of voting is held, or some other system is invoked in the case of a tie). Because of this, we assume for the sake of simplicity and consistency that there is a winner after a single round of **Simple Majority** voting.
- Universality

#### *Ranked Choice Voting (RCV)*
(TODO: go through preds and use comments i wrote to inform the things discussed here)
- Ties in rounds are randomly solved (model abstraction)
- Instead of having one chocie per candidate, we ask to rank 3 of the choices
- We enforce that there is a candidate for each choice (one, not lone)
