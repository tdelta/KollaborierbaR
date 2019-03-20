package repository;

import javax.persistence.Entity;
import javax.persistence.Id;
import javax.persistence.GeneratedValue;
import javax.persistence.OneToMany;
import javax.persistence.ManyToOne;

import proofutil.ObligationResult;

import java.util.List;

@Entity
public class MethodContract {

  public MethodContract(){}

  public MethodContract(final int number, final String methodName){
    this.number = number;
    this.methodName = methodName;
  }

  public void setFile(final File file){
    this.file = file;
  }

  public String getMethodName(){
    return methodName;
  }

  public long getIdTest(){
    return id;
  }

  @Id
  @GeneratedValue
  private Long id;

  private int number;

  private String methodName;

  @ManyToOne
  private File file;

  //@OneToMany
  //private List<ObligationResult> proofTrees;
}
