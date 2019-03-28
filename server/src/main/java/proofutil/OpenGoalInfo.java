package proofutil;

import com.fasterxml.jackson.annotation.JsonIgnore;
import javax.persistence.Entity;
import javax.persistence.GeneratedValue;
import javax.persistence.Id;
import javax.persistence.Lob;

/**
 * This class is used as a container for open goals that defines a table in the database and is also
 * used as a response type for api routes. Fields annotated with JsonIgnore will not be included in
 * api routes
 *
 * <p>It is based on the data provided by {@link de.uka.ilkd.key.proof.Goal}.
 *
 * @author Jonas Belouadi
 */
@Entity
public class OpenGoalInfo {

  @JsonIgnore @Id @GeneratedValue private long primaryKey;

  private long id;
  @Lob private String sequent;
  private String formula;

  public OpenGoalInfo() {}

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
