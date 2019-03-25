package projectmanagement;

/**
 * Structure of the FileUpdateData send by clients. It is meant to be used as a data container for
 * Java Spring Marshalling, so that request contents can be easily read and handled by server
 * methods.
 */
public class FileUpdateData {

  public String fileName;
  public String fileContent;

  /**
   * Constructor of the class
   *
   * @param fileName of the updated File
   * @param fileContent of the updated File
   */
  public FileUpdateData(String fileName, String fileContent) {
    this.fileName = fileName;
    this.fileContent = fileContent;
  }

  /** getter for the filename */
  public String filefileName() {
    return this.fileName;
  }

  /** getter for the filecontent */
  public String filecontent() {
    return this.fileContent;
  }

  /**
   * setter for the Filename
   *
   * @param fileName which will be set
   */
  public void setFileName(String fileName) {
    this.fileName = fileName;
  }

  /**
   * setter for the FileContent
   *
   * @param fileContent which will be set
   */
  public void setFileContent(String fileContent) {
    this.fileContent = fileContent;
  }
}
