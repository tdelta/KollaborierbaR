package server;

import java.util.concurrent.atomic.AtomicLong;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.RestController;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import projectmanagement.*;

@RestController
@RequestMapping("/projects")
public class ProjectController {

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

    @RequestMapping("/showProject")
    public FolderItem showProject(){

        String name = "p4";


        File file = new File("/home/marc/TestProjects");
        File[] files = file.listFiles();


        File selected = selectProjectFromArray(files, name);

        return createFolderItem(selected);
    }

    public FolderItem createFolderItem(File file){
        List<Item> entries = new LinkedList<Item>();

        for(File f: file.listFiles()){
            if(f.isFile()){
                entries.add(new FileItem(f.getName()));
            }else{
                entries.add(createFolderItem(f));
            }
        }
        return new FolderItem(entries, file.getName());

    } 


    public File selectProjectFromArray(File[] files, String name){

        for(File f : files){

            if(f.getName().equals(name)){
                return f;
            }
        }
        return null;
    }
}