package proofutil;
import java.util.List;
import java.util.ArrayList;

/**
 * This class is used as a container for open goals
 * @author Jonas Belouadi
 */
public class Obligation{
    private int id;
    private String sequent;
    
    public Obligation(int id, String sequent) {
    	this.id = id;
    	this.sequent = sequent;
    }

    public int getId(int id){
        return id;
    }

    public String getSequent(){
        return sequent;
    }
}
