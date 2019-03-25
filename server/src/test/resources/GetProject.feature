Feature: Get the structure of a specific project (GET /projects/{projectname})
Scenario: Get the structure of a specific project (GET /projects/{projectname})

# Cleanup possible old data (from past tests)
* call read('HttpApiTestCleanUp.feature')

# Setup /projects
* call read('HttpApiTestSetup.feature')



Given url 'http://localhost:9000/projects/testProject1'
And request {}
When method get
And match response == 
"""
{
  "name": "testProject1",
  "type": "folder",
  "contents": [
    {
      "name": "testFolder2",
      "type": "folder",
      "contents": [
        {
          "name": "testSubFolder2",
          "type": "folder",
          "contents": []
        },
        {
          "name": "testSubFolder3",
          "type": "folder",
          "contents": [
            {
              "name": "testSubFile1",
              "type": "file"
            }
          ]
        },
        {
          "name": "testSubFolder1",
          "type": "folder",
          "contents": []
        }
      ]
    },
    {
      "name": "testFolder1",
      "type": "folder",
      "contents": [
        {
          "name": "testFile1",
          "type": "file"
        },
        {
          "name": "testFile2",
          "type": "file"
        },
        {
          "name": "testFile3",
          "type": "file"
        }
      ]
    }
  ]
}
"""

# Cleanup all data created with setup
#* call read('HttpApiTestCleanUp.feature')