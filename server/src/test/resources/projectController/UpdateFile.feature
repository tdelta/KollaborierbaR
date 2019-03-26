Feature: Update file (fileText and fileName) (POST /projects/)


Background:

# Cleanup possible old data (from past tests)
* call read('HttpApiTestCleanUp.feature')

# Setup /projects
* call read('HttpApiTestSetup.feature')

Scenario: Update fileContent of testProject1/testFolder1/testFile1 

Given url 'http://localhost:9000/projects/testProject1/testFolder1/testFile1'
And request {"fileContent" : "Test2"}
When method post
Then status 200

Given url 'http://localhost:9000/projects/testProject1/testFolder1/testFile1'
And request {}
When method get
Then status 200
And match response contains
"""
{"fileText" : "Test2"}
"""

Scenario: Update fileName of testProject1/testFolder1/testFile1 

Given url 'http://localhost:9000/projects/testProject1/testFolder1/testFile1'
And request {"fileName" : "/projects/testProject1/testFolder1/testFile1Rename"}
When method post
Then status 200

# Check whether /projects/testProject1/testFolder1/testFile1Rename exists
Given url 'http://localhost:9000/projects/testProject1/testFolder1/testFile1Rename'
And request {}
When method get
Then status 200

Scenario: Update file which dont exists (supposed to throw error)

Given url 'http://localhost:9000/projects/testProject1/fileWhichDontExists'
And request {"fileName" : "/projects/testProject1/tryToRename"}
When method post
Then status 400


# Cleanup possible old data (from past tests)
* call read('HttpApiTestCleanUp.feature')