package synchronization.data;

/**
 * This class defines a type used in Delta.java
 * Deltas are used to communicate changes in a document with the ace editor
 */
public class Position {

    private int digit;
    private String siteId;

    public int getDigit(){
        return digit;
    }

    public String getSiteId(){
        return siteId;
    }
}
