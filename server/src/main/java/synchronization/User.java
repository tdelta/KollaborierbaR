package synchronization;

import java.util.List;

/** User Model holding Information that we assign to users of the Websocket. */
public class User {

  private String firstName;
  private String lastName;
  private int crdtId;
  private int idInProject;

  public User(
      final String firstName, final String lastName, final int crdtId, final int idInProject) {
    this.firstName = firstName;
    this.lastName = lastName;
    this.crdtId = crdtId;
  }

  /**
   * Sets the id of a user to the highest id present in the project plus one.
   *
   * @param usersInProject List of information about all users that are connected to a given project
   */
  public void setUniqueIdForProject(List<User> usersInProject) {
    idInProject =
        usersInProject.stream()
                // Get a list of ids in the project
                .map(user -> user.getIdInProject())
                // Find the highest id and add 1
                .reduce(0, (a, b) -> a > b ? a : b)
            + 1;
  }

  public void setIdInProject(int idInProject) {
    this.idInProject = idInProject;
  }

  public void setCrdtId(int crdtId) {
    this.crdtId = crdtId;
  }

  /** @return the users unique id in the project that he is working on */
  public int getIdInProject() {
    return idInProject;
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
