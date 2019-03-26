Feature: Open File with fileContent und fileName (GET /projects/)


Background:
# Cleanup possible old data (from past tests)
* call read('HttpApiTestCleanUp.feature')

# Setup /projects
* call read('HttpApiTestSetup.feature')


Scenario: Request a file which is present on the server
	
# Load testProject1/testFolder2/testSubFolder3/testSubFile1
Given url 'http://localhost:9000/projects/testProject1/testFolder2/testSubFolder3/testSubFile1'
When method get
And request {}
Then status 200
And match response contains 
"""
{"fileName" : "testSubFile1"}
"""
And match response contains
"""
{"fileText" : "Test1"}
"""

Scenario: Request a file which isn't present on the server

Given url 'http://localhost:9000/projects/testProject1/someFileWhichDontExist'
When method get
And request {}
Then status 404


# Cleanup all data created with setup
* call read('HttpApiTestCleanUp.feature')