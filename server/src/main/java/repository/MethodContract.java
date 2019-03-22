package repository;

import javax.persistence.Entity;
import javax.persistence.Id;
import javax.persistence.GeneratedValue;
import javax.persistence.OneToMany;
import javax.persistence.ManyToOne;
import javax.persistence.OneToOne;
import javax.persistence.Column;

import proofutil.ObligationResult;
import proofutil.ProofNode;

import java.util.List;
import java.util.LinkedList;

@Entity
public class MethodContract {

  public MethodContract(){}

  public MethodContract(int number){
    this.number = number;
  }

  public void setFile(final File file){
    if(file != null){
        file.addMethodContract(number,this);
    }
    this.file = file;
  }

  public Long getId(){
    return id;
  }

  public List<ObligationResult> getHistory(){
    if(history == null){
      history = new LinkedList<>();
    }
    return history;
  }

  public ObligationResult getLast(){
    return last;
  }

  public void setLast(ObligationResult result){
    this.last = result;
  }

  public void addToHistory(ObligationResult result){
    if(result != null){
      result.setMethodContract(this);
    }
    if(history == null){
      history = new LinkedList<>();
    }
    history.add(result);
  }

  @Id
  @GeneratedValue
  private Long id;

  @Column(name = "number")
  private int number;

  @ManyToOne
  private File file;

  @OneToMany(orphanRemoval=true,mappedBy="methodContract")
  private List<ObligationResult> history;

  @OneToOne(orphanRemoval=true)
  private ObligationResult last;
}
