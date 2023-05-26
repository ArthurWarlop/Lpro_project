# Group Identification

 - Evandro Giovanini, ist1105702, efgiovanini@gmail.com
 - Arthur Warlop, ist1104786, Email
 - Yahya Makhlouf, ist1107658, Email yahya.makhlouf2@gmail.com

# Implemented Features
Below is a list of features we've implemented. We've listed the main author of 
each feature, but all group members contributed to all features.

| Task                                     | Main author   |
| ---------------------------------------- | :---------:   |
| README file properly filled in           |               |
| **Task 1 (Imp.v)**                       |  Yahya        |
| Extend `com`                             |               |
| New notation                             |               |
| Examples `p1` and `p2`                   |               |
| **Task 2 (Interpreter.v)**               |               |
| Implementation of step-indexed evaluator |Yahya & Evandro|
| Proof of `equivalence1`                  |    Yahya      |
| Proof of `inequivalence1`                |    Yahya      |
| Proof of `p1_equivalent_p2`              |    Yahya      |
| **Task 3 (RelationalEvaluation.v)**      |               |
| Definition of `ceval`                    |  Arthur       |
| Proof of `break_ignore`                  |  Arthur       |
| Proof of `while_continue`                |  Arthur       |
| Proof of `while_stops_on_break`          |  Arthur       |
| Proof of `seq_continue`                  |  Arthur       |
| Proof of `seq_stops_on_break`            |  Arthur       |
| Proof of `while_break_true`              |  Yahya        |
| **Task 3 (AdditionalProperties.v)**      |Yahya & Arthur |
| Proof of `ceval_step_more`               |               |
| Proof of `ceval_step__ceval`             |               |
| Proof of `ceval__ceval_step`             |               |
| Informal proof of `ceval_deterministic'` |               |

# Extras
In addition, we've implemented the following features:

| **Extra goals**                          | Evandro     |
| Improvement of step-indexed evaluator    |             |

The improvement implementation is in Interpreter.v, using:
result', ceval_step', equivalence1' and inequivalence1'.
