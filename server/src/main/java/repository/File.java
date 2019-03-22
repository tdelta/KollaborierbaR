package repository;

import javax.persistence.Id;
import javax.persistence.GeneratedValue;
import javax.persistence.OneToMany;
import javax.persistence.Entity;
import javax.persistence.MapKey;
import javax.persistence.Column;
import javax.persistence.Table;
import javax.persistence.UniqueConstraint;
import javax.persistence.FetchType;

import java.util.Map;
import java.util.HashMap;

@Entity
@Table(uniqueConstraints = {@UniqueConstraint(columnNames = "name")})
public class File {

  public File(){}

  public File(final String name){
    this.name = name;
  }

  public String getName(){
    return name;
  }

  public Map<Integer, MethodContract> getObligations(){
    if(obligations == null){
        obligations = new HashMap<>();
    }
    return obligations;
  }

  public void addMethodContract(int number, MethodContract methodContract){
    obligations.put(number,methodContract);
  }

  @Id
  @GeneratedValue
  private Long id;

  @Column(unique=true)
  private String name;

  @OneToMany(fetch=FetchType.EAGER)
  @MapKey(name = "number")
  private Map<Integer, MethodContract> obligations;
}
