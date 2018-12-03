package projectmanagement;

/**
 * Contains contents of a file and metadata (filename).
 * It is meant to be used as a data container for Java Spring Marshalling,
 * so that file contents can be sent to clients.
 * 
 * @author Marc Arnold
 */
public class OpenedFileResponse {
	private final String filename;
	private final String filetext;

	/**
	 * Basic constructor for this class 
	 *
	 * @param name of the a file
	 * @param text content of a file
	 */
	public OpenedFileResponse(final String name, final String text) {
		this.filename = name;
		this.filetext = text;
	}
	
	/**
	 * Basic getter for filename
	 * 
	 * @return filename of the opened file
	 */
	public String getFileName() {
		return this.filename;
	}
	
	/**
	 * Basic getter for the filename
	 * 
	 * @return name of the opened file
	 */
	public String getFileText() {
		return this.filetext;
	}
	
}
