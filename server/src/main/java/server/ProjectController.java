package server;

import org.springframework.http.HttpStatus;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.*;

import org.springframework.web.servlet.HandlerMapping;
import projectmanagement.*;

import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import java.util.Scanner;

import java.util.NoSuchElementException;

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
            } else if (f.isDirectory()) {
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
     * and its name.
     * 
     * @param fileRequest to the file, which is supposed to be opened.
     * @return object containing filename and filetext (object for marshalling)
     */
    @RequestMapping("/openFile")
    @ResponseBody
    public OpenedFileResponse openFile(@RequestBody FileRequest fileRequest) throws IOException{
    	try {
        final File file = new File(projectPath + fileRequest.getPath());

        final String content = new Scanner( //scanners allow to read a file until a delimiter
            file,
            "utf-8"
        ).useDelimiter("\\Z").next(); // read until end of file (Z delimiter)
        //^ using a scanner may not be optimal (could cause overhead),
        //  but simplifies this code so much, that we keep it for now
      
        return new OpenedFileResponse(file.getName(), content);
      }
      
      // TODO implement proper error handling (appropriate status code etc.)
      catch (FileNotFoundException e) {
        e.printStackTrace();

        return new OpenedFileResponse(
            "Not found",
            "Die Datei konnte nicht geöffnet werden. Der folgende Path wurde genutzt:"
            + projectPath + fileRequest.getPath()
        );
      }	

      catch (NoSuchElementException e) {
        e.printStackTrace();

        return new OpenedFileResponse(
            "Read error",
            "Fehler beim Einlesen der angefragten Datei:"
            + projectPath + fileRequest.getPath()
        );
      }	

      catch (IllegalStateException e) {
        e.printStackTrace();

        return new OpenedFileResponse(
            "Read error",
            "Fehler beim Einlesen der angefragten Datei:"
            + projectPath + fileRequest.getPath()
        );
      }	
    }

    @RequestMapping(value = {"/**"}, method = RequestMethod.PUT)
    @ResponseBody
    public ResponseEntity createFile(@RequestParam("type") String type,HttpServletRequest request) throws IOException {

    	//TODO: Schönere Lösung finden!
    	String path = ((String) request.getAttribute( HandlerMapping.PATH_WITHIN_HANDLER_MAPPING_ATTRIBUTE )).substring(1);
    	File file = new File(path);
    	
    	if(type.equals("file")) {
    		file.createNewFile();
    	} else if(type.equals("folder")) {
    		file.mkdir();
    	} else {
    		return new ResponseEntity(HttpStatus.BAD_REQUEST);
    	}
    	return new ResponseEntity(HttpStatus.OK);
    }

    /**
     * This method handels delete requests to files, folders and projects
     *
     *
     * @return Http Response Code depending on whether the request off successful or not.
     * @throws IOException
     */
    @RequestMapping(value = {"/**"}, method = RequestMethod.DELETE)
    @ResponseBody
    public ResponseEntity deleteFile(HttpServletRequest request) throws IOException{
    	
    	//TODO: Schönere Lösung finden!
        String path = ((String) request.getAttribute( HandlerMapping.PATH_WITHIN_HANDLER_MAPPING_ATTRIBUTE )).substring(1);

        File file = new File(path);
        //check if the given path actually leads to a valid directory
        if(!file.exists()){
            //System.out.println("error");
        	return new ResponseEntity(HttpStatus.NOT_FOUND);
        }else{
            delete(file);
            return new ResponseEntity(HttpStatus.OK);
        }
    }

    /**
     * Helper method that handles the deletion of a giving file type.
     * Needs to be called recursively to delete a folders content.
     *
     * @param file File or directory that is supposed to be deleted.
     * @throws IOException
     */
    private void delete(File file) throws IOException{
        // if the currenct file is not a file but a directory we need to delete its content first.
        if(file.isDirectory()){
            if(file.list().length==0){
                //if the current directory is empty, delete it
                file.delete();
            }else{
                //if the current directory is not empty  list its content and call delete recursively
                for(File f: file.listFiles()){
                    delete(f);
                }
                //do not forget to delete the current directory itself
                file.delete();
            }
        }else{
            //if the current directory is not a directory but a file, delete it
            file.delete();
        }
    }

    // TODO: Proper HTTP error handler
    ///@ExceptionHandler({NoSuchElementException.class, IllegalStateException.class})
}
