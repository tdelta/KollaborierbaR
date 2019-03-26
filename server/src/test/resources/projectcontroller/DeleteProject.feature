Feature: Deletion of projects

Background:
# Cleanup possible old data (from past tests)
* call read('HttpApiTestCleanUp.feature')

# Setup /projects
* call read('HttpApiTestSetup.feature')


Scenario: Succesfully delete a project 

# delete testProject1
Given url 'http://localhost:9000/projects/testProject1'
And request {}
When method delete
Then status 200

# check that testProject1 isn't in the list of all projects anymore
Given url 'http://localhost:9000/projects'
And request {}
When method get
Then status 200
And match response !contains ["testProject1"]


Scenario: Unsuccesfully delete a project 

# try to delete project which doesn't exists
Given url 'http://localhost:9000/projects/testProject10'
And request {}
When method delete
Then status 404


# Cleanup possible old data created with setup
* call read('HttpApiTestCleanUp.feature')