Feature: Project Life Cycle
Scenario: Project Life Cycle

# Check whether the initial state of /projects is correct
Given url 'http://localhost:9000/projects'
When method get
Then status 200
And match response contains ["My Project", "JMLProject", "SimpleJML", "HelloWorld"]

# Add a project with the name ProjectCreatedByTest
Given url 'http://localhost:9000/projects/ProjectCreatedByTest?type=folder'
And request {}
When method put
Then status 200

# Check whether the new projects shows in the list of projects
Given url 'http://localhost:9000/projects'
When method get
Then status 200
And match response contains ["My Project", "JMLProject", "SimpleJML", "HelloWorld", "ProjectCreatedByTest"]

# Delete the created projects ProjectCreatedByTest
Given url 'http://localhost:9000/projects/ProjectCreatedByTest'
When method delete
Then status 200

# Check whether the project was correctly deleted
Given url 'http://localhost:9000/projects/'
When method get
Then status 200
And match response contains ["My Project", "JMLProject", "SimpleJML", "HelloWorld"]
