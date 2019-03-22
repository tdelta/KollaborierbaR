package proofutil;

import javax.persistence.Entity;
import javax.persistence.Id;
import javax.persistence.GeneratedValue;
import javax.persistence.ManyToOne;

/**
 * This class is used as a container for open goals
 *
 * @author Jonas Belouadi
 */
@Entity
public class OpenGoalInfo {

  //@ManyToOne(name="obligationResult")
  //private ObligationResult obligationResult

  @Id
  @GeneratedValue
  private long primaryKey;

  private long id;
  private String sequent;
  private String formula;

  public OpenGoalInfo(){}

  public OpenGoalInfo(long id, String sequent, String formula) {
    this.id = id;
    this.sequent = sequent;
    this.formula = formula;
  }

  public long getId() {
    return id;
  }

  public String getSequent() {
    return sequent;
  }

  public String getFormula() {
    return formula;
  }
}
