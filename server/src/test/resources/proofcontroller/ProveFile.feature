Feature: Proving method contracts of files

Scenario: Setup
* call read('SetupKeyProject.feature')

Scenario: Successful proof with index
# Request proof for index 0
Given url 'http://localhost:9000/proof/testProject5/Test.java?obligationIdxs=0'
And request {}
When method get
Then call read('DefineTypes.feature')
And match response ==
"""
{
  errors:[],
  failed:[],
  stackTraces:[],
  succeeded:[
    {
      "kind": "success",
      "obligationIdx": 0,
      "openGoals": [],
      "proofTree": "#(proofTreeSchema)",
      "resultMsg": "#string",
      "targetName": "#string"
    }
  ]
}
"""

Scenario: Prove all contracts with success and failure

# Request proofs for all indices
Given url 'http://localhost:9000/proof/testProject5/Test.java'
And request {}
When method get
Then call read('DefineTypes.feature')
And match response ==
"""
{
  errors:[],
  failed:[
    {
      "kind": "failure",
      "obligationIdx": 1,
      "openGoals": "#[] openGoalSchema",
      "proofTree": "#(proofTreeSchema)",
      "resultMsg": "#string",
      "targetName": "#string"
    }
  ],
  stackTraces:[],
  succeeded:[
    {
      "kind": "success",
      "obligationIdx": 0,
      "openGoals": [],
      "proofTree": "#(proofTreeSchema)",
      "resultMsg": "#string",
      "targetName": "#string"
    }
  ]
}
"""

Scenario: Cleanup

Given url 'http://localhost:9000/projects/testProject5'
And request {}
When method delete
Then status 200
