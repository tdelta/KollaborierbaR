Feature: Open File with fileContent und fileName (GET /projects/)
Scenario: Open File with fileContent und fileName (GET /projects/)


# Load testProject1/testFolder2/testSubFolder3/testSubFile1
Given url 'http://localhost:9000/projects/testProject1/testFolder2/testSubFolder3/testSubFile1'
And request {}
When method get
And response contains 
"""
{"filename" : "testSubFile1"}
"""
And response contains
"""
{"filetext" : "Test1"}
"""