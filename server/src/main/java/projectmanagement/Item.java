package projectmanagement;

public class Item{

    private String name;
    protected String Typ;

    public Item(String name){

        this.name = name;

    }

    public String getName(){

        return this.name;

    }

    public String getTyp(){

        return this.Typ;

    }

}