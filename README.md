



Choices/Challenges:

### **Abstractions/Choices in Voting Systems**   
*Simple Majority:*   
- For Simple Majority we abstract out the cases where there are ties (we enforce that *some candidate* has the most amount of votes and therefore wins). 
  - We do this because we are only interested in the cases where elections can be *won* by two *distinct* candidates in response to a single violation of one of *Arrow's Fairness Principles* (not the cases where there is a winner/tie in response to a violation).
  - Importantly, we note that there are external mechanisms not native to a **Simple Majority** voting system that handle the situation in case of a tie. (Usually, another round of voting is held, or some other system is invoked in the case of a tie). Because of this, we assume for the sake of simplicity and consistency that there is a winner after a single round of **Simple Majority** voting.
- Universality