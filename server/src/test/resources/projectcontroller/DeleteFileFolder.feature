Feature: Deletion of files and folders

Background:
# Cleanup possible old data (from past tests)
* call read('HttpApiTestCleanUp.feature')

# Setup /projects
* call read('HttpApiTestSetup.feature')


Scenario: Delete a folder from testProject1

# Delete testProject1/testFolder1
Given url 'http://localhost:9000/projects/testProject1/testFolder1'
And request {}
When method delete
Then status 200

# Check that testProject1/testFolder1 doesn't exists anymore
Given url 'http://localhost:9000/projects/testProject1'
And request {}
When method get
Then status 200
And match response.contents !contains {name: "testFolder1", type : "folder", content : '#ignore'}


Scenario: Delete a file from testProject1/testFolder1


Given url 'http://localhost:9000/projects/testProject1/testFolder1/testFile1'
And request {}
When method delete
Then status 200

# Check that testProject1/testFolder1/testFile1 doesn't exists anymore
Given url 'http://localhost:9000/projects/testProject1'
And request {}
When method get 
Then status 200
Then def testFolder1Contents =
"""
[
	{
		name : "testFile1",
		type : "file"
	}
]
"""
Then def projectContents = 
"""
	{
		name : "testFolder1",
		type : "folder",
		contents : '#(!^testFolder1Contents)'
	}
"""
And match response contains 
"""
{
	name : "testProject1",
	type : "folder",
	contents : '#(^projectContents)'
}
"""

Scenario: Delete a folder from testProject1 which doesn't exist (supposed to throw error)

Given url 'http://localhost:9000/projects/testProject1/FolderDontExist'
And request {}
When method delete
Then status 404


* call read('HttpApiTestCleanUp.feature')

