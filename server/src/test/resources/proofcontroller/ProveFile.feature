Feature: Proving method contracts of files

Scenario: Setup
* call read('SetupKeyProject.feature')

Scenario: Successful proof with index
# Request proof for index 0
Given url 'http://localhost:9000/proof/testProject5/Test.java?obligationIdxs=0'
And request {}
When method get
Then call read('DefineTypes.feature')
And status 200
And match response ==
"""
{
  failed:[],
  succeeded:[
    {
      "id": null,
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
And status 200
And match response ==
"""
{
  failed:[
    {
      "id": null,
      "kind": "failure",
      "obligationIdx": 1,
      "openGoals": "#[] openGoalSchema",
      "proofTree": "#(proofTreeSchema)",
      "resultMsg": "#string",
      "targetName": "#string"
    }
  ],
  succeeded:[
    {
      "id": null,
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
Scenario: Proving a file with syntax errors leads to a single error

# Insert incorrect java code into the test file
Given url 'http://localhost:9000/projects/testProject5/Test.java'
And request { fileContent: "mlem" }
When method post
Then status 200

# Request proofs for all contracts of the file 
Given url 'http://localhost:9000/proof/testProject5/Test.java'
And request {}
When method get
Then call read('DefineTypes.feature')
And status 200
And match response ==
"""
{
  succeeded: [],
  failed: [],
}
"""

Scenario: Cleanup

Given url 'http://localhost:9000/projects/testProject5'
And request {}
When method delete
Then status 200
