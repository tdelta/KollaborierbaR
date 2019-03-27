Feature: Setup a provable file

Scenario: Create file and project
# Create testProject5
Given url 'http://localhost:9000/projects/testProject5?type=folder'
And request {}
When method put
Then status 200

# Create Test.java
Given url 'http://localhost:9000/projects/testProject5/Test.java?type=file'
And request {}
When method put
Then status 200

# Insert java and jml into the file
Given url 'http://localhost:9000/projects/testProject5/Test.java'
And request { fileContent: "public class Test {\n/*@ normal_behavior\n  @ ensures \\result == x + y;\n  @*/\npublic static int add(int x, int y) {\n   return x + y;\n}\n\n/*@ normal_behavior\n  @ ensures \\result == x + y;\n  @*/\npublic static int sub(int x, int y) {\n   return x - y;\n}\n}" }
When method post
Then status 200
