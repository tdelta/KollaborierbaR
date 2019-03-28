Feature: Prove Contract using a macro file

Scenario: Setup
* call read('SetupKeyProject.feature')

# Create a macro file in the project
Given url 'http://localhost:9000/projects/testProject5/Test.script?type=file'
And request {}
When method put
Then status 200

# Insert rubbish into the macro file to generate an error
Given url 'http://localhost:9000/projects/testProject5/Test.script'
And request { fileContent: "mulm" }
When method post
Then status 200


# Request proof for index 0 and expect an error
Given url 'http://localhost:9000/proof/testProject5/Test.java?obligationIdxs=0&macro=/Test.script'
And request {}
When method get
Then status 200
And call read('DefineTypes.feature')
And match response ==
"""
{
  succeeded: [],
  failed: [],
  errors: "#[1] ^error",
  stackTraces: "#[1] ^error",
}
"""

# Request proofs for all obligations and expect errors
Given url 'http://localhost:9000/proof/testProject5/Test.java?macro=/Test.script'
And request {}
When method get
Then status 200
And call read('DefineTypes.feature')
And match response ==
"""
{
  succeeded: [],
  failed: [],
  errors: "#[2] ^error",
  stackTraces: "#[2] ^error",
}
"""

Scenario: Cleanup

Given url 'http://localhost:9000/projects/testProject5'
And request {}
When method delete
Then status 200
