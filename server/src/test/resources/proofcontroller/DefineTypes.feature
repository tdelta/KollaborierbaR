@ignore
Feature:

Scenario:
* def openGoalSchema =
"""
{
  "formula": "#string",
  "id": "#number",
  "sequent": "#string"
}
"""
* def proofTreeSchema = 
"""
{
  "children":"#[] proofTreeSchema",
  "kind": "#regex ClosedProofTree|OneStepSimplification|OpenProofTree|BranchNode|OpenGoal|ClosedGoal|InteractiveGoal|LinkedGoal|DefaultNode",
  "oneStepId": "#number",
  "sequent": "#string",
  "serialNr": "#number",
  "text": "#string"
}
"""
