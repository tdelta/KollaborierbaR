package projectmanagement;

/**
 * This class is a data container for Java Springs Marshalling. There are 
 * two types of Items: folder and files. For both there are additional classes
 * which extend this one.
 * 
 * @author David Heck, Marc Arnold
 *
 */
public class Item{

    private String name;
    protected String Typ;

    
    /**
     * This is the default constructor for the class
     * 
     * @param name of the item
     */
    public Item(String name){

        this.name = name;

    }

    /**
     * 
     * Basic getter of the name.
     * 
     * @return name of the item
     */
    public String getName(){

        return this.name;

    }

    /**
     * 
     * Basic getter of the Typ
     * 
     * @return the type of the item (folder/file) 
     */
    public String getTyp(){

        return this.Typ;

    }

}