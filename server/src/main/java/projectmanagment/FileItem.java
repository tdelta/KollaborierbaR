package projectmanagment;

public class FileItem extends Item{

    public FileItem(String name){
    
        super(name);
        Typ = "file";
    }

    public String getTyp(){
        return this.Typ;
    }

}