package server;

import java.util.concurrent.atomic.AtomicLong;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.RestController;

import projectmanagement.*;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

/**
 * @author Marc Arnold, David Heck
 *  This is a rest controller for handling the project file structure
 */
@RestController
@RequestMapping("/projects")
public class ProjectController {

    /**
     * That method handels requests to /listProjects and creates a list of project names. 
     *
     * @return a LinkedList containing the Projects from the Projects folder(currently hardcoded)
     */
    @RequestMapping("/listProjects")
    public List<FolderItem> listProjects() {
        List<FolderItem> projects = new LinkedList<FolderItem>();

        File file = new File("/home/marc/TestProjects/");
        File[] files = file.listFiles();

        for(File f: files){

            projects.add(new FolderItem(null, f.getName()));
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
        File file = new File("/home/marc/TestProjects");
        File[] files = file.listFiles();


        File selected = selectProjectFromArray(files, name);

        return createFolderItem(selected);
    }

    /**
     * Helper function for recursivly creating a folderItem object from a given file structure.
     *
     * @param file A file from the file system
     * @return A Folder and its content 
     */
    public FolderItem createFolderItem(File file){
        List<Item> entries = new LinkedList<Item>();

        // Adding the content of the Folder to a list if it is a file just add it if its a folder add it and call the method again recursivly
        for(File f: file.listFiles()){
            if(f.isFile()){
                entries.add(new FileItem(f.getName()));
            }else{
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
        for(File f : files){
            if(f.getName().equals(name)){
                return f;
            }
        }
        return null;
    }
}