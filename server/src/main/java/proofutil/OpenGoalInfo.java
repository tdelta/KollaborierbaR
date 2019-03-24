package proofutil;

/**
 * This class is used as a container for open goals
 *
 * @author Jonas Belouadi
 */
public class OpenGoalInfo {
  private long id;
  private String sequent;
  private String formula;

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
