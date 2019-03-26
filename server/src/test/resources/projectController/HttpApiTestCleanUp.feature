# This feature file isn't a test by it self. It is supposed
# to be called (with call read ('HttpApiTestCleanUp.feature')) after
# testing other Features/Scenarios
Feature: CleanUp for Http Api Testing
Scenario: CleanUp for Http Api Testing

#CleanUp all projects created with HttpApiTestSetup.feature
Given url 'http://localhost:9000/projects/testProject1'
And request {}
When method delete

Given url 'http://localhost:9000/projects/testProject2'
And request {}
When method delete

Given url 'http://localhost:9000/projects/testProject3'
And request {}
When method delete