# This feature file isn't a test all by it self. It is supposed
# to be called (with call read ('HttpApiTestSetup.feature')) before
# testing other Features/Scenarios
Feature: Setup for Http Api Testing
Scenario: Setup for Http Api Testing

#Create testProject1
Given url 'http://localhost:9000/projects/testProject1?type=folder'
And request {}
When method put

#Create testProject2
Given url 'http://localhost:9000/projects/testProject2?type=folder'
And request {}
When method put

#Create testProject3
Given url 'http://localhost:9000/projects/testProject3?type=folder'
And request {}
When method put

#Create testProject1/testFolder1
Given url 'http://localhost:9000/projects/testProject1/testFolder1?type=folder'
And request {}
When method put

#Create testProject1/testFolder1/testFile1
Given url 'http://localhost:9000/projects/testProject1/testFolder1/testFile1?type=file'
And request {}
When method put

#Create testProject1/testFolder1/testFile2
Given url 'http://localhost:9000/projects/testProject1/testFolder1/testFile2?type=file'
And request {}
When method put

#Create testProject1/testFolder1/testFile3
Given url 'http://localhost:9000/projects/testProject1/testFolder1/testFile3?type=file'
And request {}
When method put

#Create testProject1/testFolder2/
Given url 'http://localhost:9000/projects/testProject1/testFolder2?type=folder'
And request {}
When method put

#Create testProject1/testFolder2/testSubFolder1
Given url 'http://localhost:9000/projects/testProject1/testFolder2/testSubFolder1?type=folder'
And request {}
When method put

#Create testProject1/testFolder2/testSubFolder2
Given url 'http://localhost:9000/projects/testProject1/testFolder2/testSubFolder2?type=folder'
And request {}
When method put

#Create testProject1/testFolder2/testSubFolder3
Given url 'http://localhost:9000/projects/testProject1/testFolder2/testSubFolder3?type=folder'
And request {}
When method put

#Create testProject1/testFolder2/testSubFolder3/testSubFile1
Given url 'http://localhost:9000/projects/testProject1/testFolder2/testSubFolder3/testSubFile1?type=file'
And request {}
When method put

# Set testProject1/testFolder2/testSubFolder3/testSubFile1 fileContent
Given url 'http://localhost:9000/projects/testProject1/testFolder2/testSubFolder3/testSubFile1'
And request {"fileContent" : "Test1"}
When method post
