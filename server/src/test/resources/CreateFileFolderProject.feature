Feature: Creation of files/folders/projects


Scenario: Create project

# Create testProject4
Given url 'http://localhost:9000/projects/testProject4?type=folder'
And request {}
When method put
Then status 200

# Check whether projects/testProject4 exists
Given url 'http://localhost:9000/projects/'
When method get
And request {}
Then status 200
And match response contains ["testProject4"];


# Delete testProject4
Given url 'http://localhost:9000/projects/testProject4'
And request {}
When method delete