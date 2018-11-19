package projectmanagement;

/**
 * This class is a data container for Java Spring Marshalling.
 * 
 * 
 * @author David Heck, Marc Arnold
 *
 */
public class FileItem extends Item{

	/**
	 * This is the default constructor for the class.
	 * 
	 * @param name for the item
	 */
    public FileItem(String name){
    
        super(name);
        Typ = "file";
    }
}