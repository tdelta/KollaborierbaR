package synchronization;

public class User {

  /**
   * User Model holding Information that we assign to users of the Websocket.
   */
  private String firstName;
  private String lastName;
  private int crdtId;

  public User(String firstName, String lastName, int crdtId) {
    this.firstName = firstName;
    this.lastName = lastName;
    this.crdtId = crdtId;
  }

  public void setCrdtId(int crdtId) {
    this.crdtId = crdtId;
  }

  public int getCrdtId() {
    return crdtId;
  }

  public String getFirstName() {
    return firstName;
  }

  public String getLastName() {
    return lastName;
  }
}
