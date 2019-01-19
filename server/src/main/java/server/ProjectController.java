package server;

import java.util.concurrent.atomic.AtomicLong;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.CrossOrigin;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.ResponseBody;
import org.springframework.web.bind.annotation.RestController;
import org.springframework.context.ApplicationEventPublisher;
import org.springframework.beans.factory.annotation.Autowired;

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

import java.util.Scanner;

import java.util.NoSuchElementException;

import server.TestEvent;

/**
 * @author Marc Arnold, David Heck
 *  This is a rest controller for handling the project file structure
 */
@RestController
@CrossOrigin
@RequestMapping("/projects")
public class ProjectController {
    private static final String projectPath = "projects";

    @Autowired
    private ApplicationEventPublisher applicationEventPublisher;

    @RequestMapping("/test")
    public void test() {
        System.out.println("Publishing custom event. ");
        TestEvent customSpringEvent = new TestEvent(this, "LOL");
        applicationEventPublisher.publishEvent(customSpringEvent);
    }

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
     * @param path to the file, which is supposed to be opened.
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

    // TODO: Proper HTTP error handler
    ///@ExceptionHandler({NoSuchElementException.class, IllegalStateException.class})
}
