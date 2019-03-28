package synchronization;

public class User {

  /** User Model holding Information that we assign to users of the Websocket. */
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

  /** @return the users id in his collaborative document, unique per file */
  public int getCrdtId() {
    return crdtId;
  }

  /** @return first name for example an adjective */
  public String getFirstName() {
    return firstName;
  }

  /** @return last name for example an animal */
  public String getLastName() {
    return lastName;
  }
}
