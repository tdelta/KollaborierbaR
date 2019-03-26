package proofutil;

import com.fasterxml.jackson.annotation.JsonIgnore;
import javax.persistence.Entity;
import javax.persistence.GeneratedValue;
import javax.persistence.Id;

/**
 * This class is used as a container for open goals that defines a table in the database and is also
 * used as a response type for api routes. Fields annotated with JsonIgnore will not be included in
 * api routes
 *
 * @author Jonas Belouadi
 */
@Entity
public class OpenGoalInfo {

  @JsonIgnore @Id @GeneratedValue private long primaryKey;

  private long id;
  private String sequent;
  private String formula;

  public OpenGoalInfo() {}

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
