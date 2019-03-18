package repository;

import javax.persistence.Id;
import javax.persistence.GeneratedValue;
import javax.persistence.OneToMany;
import javax.persistence.Entity;

@Entity
public class File {

  public File(final String name){
    this.name = name;
  }

  public String getName(){
    return name;
  }

  @Id
  @GeneratedValue
  private Long id;

  private String name;
}
