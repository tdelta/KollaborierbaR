Feature: Get list of projects (GET /projects)
Scenario: Get list of projects (GET /projects)

# Cleanup possible old data (from past tests)
* call read('HttpApiTestCleanUp.feature')

# Setup /projects
* call read('HttpApiTestSetup.feature')

Given url 'http://localhost:9000/projects'
When method get
Then status 200
And match response contains ["testProject1", "testProject2", "testProject3"]

# Cleanup all data created with setup
* call read('HttpApiTestCleanUp.feature')
