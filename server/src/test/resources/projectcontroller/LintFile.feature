Feature: Request linting of java code from the server

Scenario: Lint code with an error and get the correct line and column (starting with 0)

Given url 'http://localhost:9000/lint?name=Test.java'
And request "public class Test{\npublic static void main(String[] args){\nsyntaxerror\n}\n}"
When method post
Then status 200
And match response contains
"""
{
  message: "#string",
  endCol:11,
  endRow:2,
  kind:"ERROR",
  startCol:0,
  startRow:2
}
"""

Scenario: Lint code with an unsupported feature and get the correct line and column (starting with 0)

Given url 'http://localhost:9000/lint?name=Test.java'
And request "public class Test{\nimport java.util.function.Consumer\npublic static void main(String[] args){\nConsumer<String> test = s -> {};\n}\n}"
When method post
Then status 200
And match response contains
"""
{
  message: "#string",
  endCol:31,
  endRow:3,
  kind:"NOT_SUPPORTED",
  startCol:24,
  startRow:3
}
"""
