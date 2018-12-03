package projectmanagement;

public class ProjectPath {
	
	public String path;
	
	// jackson/spring needs to be able to instantiate this class without arguments
	public ProjectPath() {}
	
	public ProjectPath(String path, String projectname){
		this.path = path;
	}
	
	public String getPath() {
		return this.path;
	}
	
	public void setPath(String path) {
		this.path = path;
	}
	
}
