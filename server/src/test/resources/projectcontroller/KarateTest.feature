Feature: Karate Test

Scenario: Karate Test
  * def x =
  """
  {
    a: 2,
    b: 1,
    c: [
      3,
      4
    ]
  }
  """
  * def z =
  """
  [
    4,
    3
  ]
  """
  * def y =
  """
  {
    c: #(^z),
    b: 1,
    a: 2
  }
  """
  * match x contains y
