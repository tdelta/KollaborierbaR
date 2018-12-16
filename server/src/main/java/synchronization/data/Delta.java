package synchronization.data;

import synchronization.data.Position;
import synchronization.data.Version;
import synchronization.data.Char;

/**
 * This class defines the format in which changes in text are communicated with the ace editor
 */
public class Delta {

    enum Type {
        insert, delete;
    }

    private Type type;
    private Version version;
    private Char character;

    public void setChar(Char character){
        this.character = character;
    }

    public Type getType(){
        return type;
    }

    public Version getVersion(){
        return version;
    }

    public Char getChar(){
        return character;
    }
}
