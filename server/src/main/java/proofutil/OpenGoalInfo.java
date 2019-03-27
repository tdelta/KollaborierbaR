package proofutil;

/**
 * This class is used as a container for open KeY goals. It contains just the data, the client needs
 * to know to display the open goal in its UI.
 *
 * <p>It is based on the data provided by {@link de.uka.ilkd.key.proof.Goal}.
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

  /** Number of proof steps, until this goal was reached. TODO: Rename to getTime */
  public long getId() {
    return id;
  }

  /** KeY Goal rendered as string, using {@link de.uka.ilkd.key.proof.Goal#toString} */
  public String getSequent() {
    return sequent;
  }

  /** KeY Goal rendered using {@link de.uka.ilkd.key.pp.LogicPrinter#quickPrintSequent}. */
  public String getFormula() {
    return formula;
  }
}
