package projectmanagement;

public class FileUpdateData {

	public String fileName;
	public String fileContent;
	
	public FileUpdateData(String fileName, String fileContent){
		this.fileName = fileName;
		this.fileContent = fileContent;
	}
	
	
	public String filefileName() {
		return this.fileName;
	}
	
	public String filecontent() {
		return this.fileContent;
	}
	
	public void setFileName(String fileName) {
		this.fileName = fileName;
	}
	
	public void setFileContent(String fileContent) {
		this.fileContent = fileContent;
	}
}
