package projectmanagement;

import java.util.List;

/**
 * This class is a data container for Java Spring Marshalling.
 * 
 * 
 * @author David Heck, Marc Arnold
 *
 */
public class FolderItem extends Item{

    public final List<Item> contents;

    
    /**
     * This is the default constructor for a FolderItem.
     * 
     * 
     * @param contents is the list of folder/files which the folder contains
     * @param name of the folder
     */
    public FolderItem(List<Item> contents, String name){

        super(name);
        this.Typ = "folder";
        this.contents = contents;
    }

    /**
     * 
     * Basic getter for contents
     * 
     * @return contents of the folderitem
     */
    public List<Item> getContents(){
        return this.contents;
    }
}