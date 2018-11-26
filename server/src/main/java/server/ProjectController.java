package server;

import java.util.concurrent.atomic.AtomicLong;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.CrossOrigin;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.ResponseBody;
import org.springframework.web.bind.annotation.RestController;

import projectmanagement.*;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.util.LinkedList;
import java.util.List;

/**
 * @author Marc Arnold, David Heck
 *  This is a rest controller for handling the project file structure
 */
@RestController
@CrossOrigin
@RequestMapping("/projects")
public class ProjectController {
    private static final String projectPath = "projects";

    /**
     * That method handels requests to /listProjects and creates a list of project names. 
     *
     * @return a List containing Stings of the Names form of the Folders in the Projects folder(currently hardcoded)
     */
    @RequestMapping("/listProjects")
    public List<String> listProjects() {
        final List<String> projects = new LinkedList<String>();

        final File file = new File(projectPath);
        final File[] files = file.listFiles();

        for(final File f: files) {
            projects.add(f.getName());
        }

        return projects;
    }

    /**
     * That method handels requests to /showProject and creates a folderItem object which models the folder structure
     * of the given folder name. The object will later be marshalled through Java Spring, resulting in a JSON object. 
     *
     * @param name is given in the http request.
     * @return the content of a chooses Projekt (currently hardcoded) in the form of a folder
     */
    @RequestMapping("/showProject")
    public FolderItem showProject(@RequestParam("name") String name){
        // Get the File/Folder form the file system
        final File file = new File(projectPath);
        final File[] files = file.listFiles();

        final File selected = selectProjectFromArray(files, name);

        return createFolderItem(selected);
    }

    /**
     * Helper function for recursivly creating a folderItem object from a given file structure.
     *
     * @param file A file from the file system
     * @return A Folder and its content 
     */
    public FolderItem createFolderItem(File file){
        final List<Item> entries = new LinkedList<Item>();

        // Adding the content of the Folder to a list if it is a file just add it if its a folder add it and call the method again recursivly
        for(final File f: file.listFiles()){
            if(f.isFile()){
                entries.add(new FileItem(f.getName()));
            } else {
                entries.add(createFolderItem(f));
            }
        }
        return new FolderItem(entries, file.getName());
    } 


    /**
     * Selectes a folder/project from a given file structure and returns it.
     *
     * @param files List of the content of a folder
     * @param name	Name of the to be selected Folder
     * @return The folder matching the giving name or null if it does not exist
     */
    public File selectProjectFromArray(File[] files, String name){
        for(final File f : files){
            if(f.getName().equals(name)){
                return f;
            }
        }
        return null;
    }
    
    /**
     * 
     * That method handels request to /openFile and returns the contents of a file
     * 
     * @param path to the file, which is supposed to be opened.
     * @return object containing filename and filetext (object for marshalling)
     */
    @RequestMapping("/openFile")
    @ResponseBody
    public OpenedFile openFile(@RequestBody ProjectPath path) throws IOException{
        	
    	File file = null;
    	InputStream filestream = null;
		
    	try {
			filestream = new FileInputStream(projectPath +path.getPath());
			file = new File(projectPath +path.getPath());
		} catch (FileNotFoundException e) {
			e.printStackTrace();
			return new OpenedFile("Not found", "Die Datei konnte nicht geöffnet werden. Der folgende Path wurde genutzt:" + projectPath+ path.getPath());
		}
    	
    	InputStreamReader filereader = new InputStreamReader(filestream, Charset.forName("UTF-8"));
    	
    	
    	String filecontent = "";
    	
    	// Start reading from file
    	int literal = filereader.read();
    	while(literal != -1) {
    		
    		//Covert integer representation of literal into a char representation
    		char convertedLiteral = (char) literal;
    		
    		// Append the returnString with the converted literal
    		filecontent = filecontent + Character.toString(convertedLiteral);
    		
    		//Read next literal;
    		literal = filereader.read();
    		
    	}
    	
    	// Finished reading from file
    	filereader.close();
    
    	return new OpenedFile(file.getName(), filecontent);
    }
    
}
