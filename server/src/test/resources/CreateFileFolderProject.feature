Feature: Creation of files/folders/projects



# This is just cleanup! If a previous test failed,
# there maybe already is a testProject4, which would
# prohibit  the test from working
Scenario: Cleanup

# Delete testProject4
Given url 'http://localhost:9000/projects/testProject4'
And request {}
When method delete


# Start the real testing
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


Scenario: Create folder within newly created testProject4


Given url 'http://localhost:9000/projects/testProject4/testSubFolder1?type=folder'
And request {}
When method put
Then status 200

# Check whether testProject4/testSubFolder1 exists
Given url 'http://localhost:9000/projects/testProject4'
And request {}
When method get
Then status 200
And match response.contents contains {name : "testSubFolder1", type : "folder", contents: [] }


Scenario: Create file within newly created testProject4/testSubFolder1/


Given url 'http://localhost:9000/projects/testProject4/testSubFolder1/testSubFile1?type=file'
And request {}
When method put
Then status 200

# Check whether testProject4/testSubFolder1/testSubFile1 exists
Given url 'http://localhost:9000/projects/testProject4'
And request {}
When method get
Then status 200 
Then def testSubFolder1Content =
"""
[
	{
		name : "testSubFile1",
		type : "file"	
	}
]
"""
And match response.contents contains {name : "testSubFolder1", type : "folder", contents: '#(^testSubFolder1Content)' }


Scenario: Try to create testProject4/testSubFolder1/testSubFile1 again (supposed to throw error)


Given url 'http://localhost:9000/projects/testProject4/testSubFolder1/testSubFile1?type=file'
And request {}
When method put
Then status 400


Scenario: Try to create file with invalid type, for example ?type = SomethingWrong (supposed th throw error)


Given url 'http://localhost:9000/projects/testProject4/testSubFolder1/testSubFile2?type=SomethingWrong'
And request {}
When method put
Then status 400

# This is cleanup!
# Delete testProject4
Given url 'http://localhost:9000/projects/testProject4'
And request {}
When method delete