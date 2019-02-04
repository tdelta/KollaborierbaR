package proofutil;

/**
 * This class is used as a container for open goals
 * @author Jonas Belouadi
 */
public class Obligation{
    private long id;
    private String sequent;
    
    public Obligation(long id, String sequent) {
    	this.id = id;
    	this.sequent = sequent;
    }

    public long getId(){
        return id;
    }

    public String getSequent(){
        return sequent;
    }
}
