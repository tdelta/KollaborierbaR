Feature: Project Life Cycle
Scenario: Project Life Cycle

# Check whether the initial state of /projects is correct
Given url 'http://localhost:9000/projects/listProjects'
When method get
Then status 200
