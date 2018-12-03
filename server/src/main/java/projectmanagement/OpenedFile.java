package projectmanagement;

/**
 * This class is a data container for Java Spring Marshalling.
 * 
 * 
 * @author Marc Arnold
 *
 */
public class OpenedFile {

	private final String filename;
	private final String filetext;
	

	/**
	 * Basic constructor for this class 
	 *
	 * @param name of the opened file
	 * @param text content of the opened file
	 */
	public OpenedFile(String name, String text) {
		this.filename = name;
		this.filetext = text;
	}
	
	/**
	 * Basic getter for filename
	 * 
	 * 
	 * @return filename of the opened file
	 */
	public String getFileName() {
		return this.filename;
	}
	
	/**
	 * Basic getter for the filename
	 * 
	 * 
	 * @return name of the opened file
	 */
	public String getFileText() {
		return this.filetext;
	}
	
}
