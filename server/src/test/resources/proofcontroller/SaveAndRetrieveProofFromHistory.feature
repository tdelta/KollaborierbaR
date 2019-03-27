Feature: Add proof results to the history and retrieve it


Scenario: Add proof results to the history


# Add a proof result with the id 0 to the history of test.java
Given url 'http://localhost:9000/proof/testProject1/test.java/obligation/0/history'
And request 
"""
{
	"kind" : "success",
	"obligationIdx" : 0,
	"openGoals" : [],
	"resultMsg" : "Message generated by test",
	"targetName" : "test1"
}
"""
When method post
Then status 200
Then def historyId = response 


# Now check that the proof result was saved in the history
Given url 'http://localhost:9000/proof/testProject1/test.java/obligation/0/history/' + historyId
And request {}
When method get
Then status 200
And match response contains
"""
{
	"kind" : "success",
	"obligationIdx" : 0,
	"openGoals" : [],
	"resultMsg" : "Message generated by test",
	"targetName" : "test1"
}
"""