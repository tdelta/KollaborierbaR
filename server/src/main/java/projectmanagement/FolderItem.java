package projectmanagement;

import java.util.List;

public class FolderItem extends Item{

    public final List<Item> contents;

    public FolderItem(List<Item> contents, String name){

        super(name);
        this.Typ = "folder";
        this.contents = contents;
    }

    public String getTyp(){
        return this.Typ;
    }

    public List<Item> getContents(){
        return this.contents;
    }
}