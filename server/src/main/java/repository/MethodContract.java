package repository;

import java.util.LinkedList;
import java.util.List;
import javax.persistence.Column;
import javax.persistence.Entity;
import javax.persistence.GeneratedValue;
import javax.persistence.Id;
import javax.persistence.ManyToOne;
import javax.persistence.OneToMany;
import javax.persistence.OneToOne;
import proofutil.ObligationResult;

/** Database table definition. */
@Entity
public class MethodContract {

  public MethodContract() {}

  public MethodContract(int number) {
    this.number = number;
  }

  /**
   * Sets the file (foreign key) and also adds the method contract to the file object
   *
   * @param file the file
   */
  public void setFile(final File file) {
    if (file != null) {
      file.addMethodContract(number, this);
    }
    this.file = file;
  }

  /** @return Primary key in the database */
  public Long getId() {
    return id;
  }

  /**
   * Returns the list of saved obligation results belonging to this method contract or an empty list
   */
  public List<ObligationResult> getHistory() {
    if (history == null) {
      history = new LinkedList<>();
    }
    return history;
  }

  /** The last executed proof */
  public ObligationResult getLast() {
    return last;
  }

  public void setLast(ObligationResult result) {
    this.last = result;
  }

  /**
   * Adds an obligation result to the list of saved obligation results. Also sets the method
   * contract field in the obligation result object
   *
   * @param result obligation result
   */
  public void addToHistory(ObligationResult result) {
    if (result != null) {
      result.setMethodContract(this);
    }
    if (history == null) {
      history = new LinkedList<>();
    }
    history.add(result);
  }

  @Id @GeneratedValue private Long id;

  // The column is named because it corresponds to the index in the hash map of the file object
  @Column(name = "number")
  private int number;

  @ManyToOne private File file;

  /**
   * orphanRemoval: If an obligation result is removed from the list it is removed from the database
   * as well mappedBy methodContract: Means the obligation result is part of this list iff its
   * method contract field is set to this object
   */
  @OneToMany(orphanRemoval = true, mappedBy = "methodContract")
  private List<ObligationResult> history;

  @OneToOne(orphanRemoval = true)
  private ObligationResult last;
}
