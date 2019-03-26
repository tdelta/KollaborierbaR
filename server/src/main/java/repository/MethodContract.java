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

/**
 * Database table definition.
 */
@Entity
public class MethodContract {

  public MethodContract(){}

  public MethodContract(int number){
    this.number = number;
  }

  /**
   * Sets the file (foreign key) and also adds the method contract to the file object
   *
   * @param file the file
   */
  public void setFile(final File file){
    if(file != null){
        file.addMethodContract(number,this);
    }
    this.file = file;
  }

  public Long getId(){
    return id;
  }

  /**
   * Returns the list of saved obligation results belonging to this method contract
   * or an empty list
   */
  public List<ObligationResult> getHistory(){
    if(history == null){
      history = new LinkedList<>();
    }
    return history;
  }

  /**
   * The last executed proof
   */
  public ObligationResult getLast(){
    return last;
  }

  public void setLast(ObligationResult result){
    this.last = result;
  }

  /**
   * Adds an obligation result to the list of saved obligation results.
   * Also sets the method contract field in the obligation result object
   *
   * @param result obligation result
   */
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
