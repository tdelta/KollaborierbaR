package projectmanagement;

/**
 * Structure of a file request as sent by clients. It is meant to be used as a data container for
 * Java Spring Marshalling, so that request contents can be easily read and handled by server
 * methods.
 *
 * <p>Such a request usually just contains a file path of the following format:
 *
 * <p>* leading slash ('/') * project name * relative path of file within project
 *
 * @author Marc Arnold
 */
public class FileRequest {
  public String path;

  // jackson/spring needs to be able to instantiate this class without arguments
  public FileRequest() {}

  public FileRequest(String path, String projectname) {
    this.path = path;
  }

  /**
   * getter for the path
   */
  public String getPath() {
    return this.path;
  }

  /**
   * setter for the path
   *
   * @param path which will set
   */
  public void setPath(String path) {
    this.path = path;
  }
}
