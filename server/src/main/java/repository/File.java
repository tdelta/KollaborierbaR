package repository;

import java.util.HashMap;
import java.util.Map;
import javax.persistence.CascadeType;
import javax.persistence.Column;
import javax.persistence.Entity;
import javax.persistence.FetchType;
import javax.persistence.GeneratedValue;
import javax.persistence.Id;
import javax.persistence.MapKey;
import javax.persistence.OneToMany;
import javax.persistence.Table;
import javax.persistence.UniqueConstraint;

/** Database table definition */
@Entity
@Table(uniqueConstraints = {@UniqueConstraint(columnNames = "name")})
public class File {

  /** Standard constructor used by hibernate to load objects from the database */
  public File() {}

  public File(final String name) {
    this.name = name;
  }

  public String getName() {
    return name;
  }

  /**
   * @return A mapping from an index in the file to the corresponding proof obligation. Empty hash
   *     map if no proof obligations are associated with the file.
   */
  public Map<Integer, MethodContract> getObligations() {
    if (obligations == null) {
      obligations = new HashMap<>();
    }
    return obligations;
  }

  /**
   * Add a proof obligation to the file
   *
   * @param number index of the proof obligation in the file
   * @param methodContract proof obligation
   */
  public void addMethodContract(int number, MethodContract methodContract) {
    obligations.put(number, methodContract);
  }

  // Primary key
  @Id @GeneratedValue private Long id;

  // There can be no two files with the same name in the database
  @Column(unique = true)
  private String name;

  // FetchType EAGER means that all obligations will be immediately loaded when the file is loaded
  // from the database
  @OneToMany(fetch = FetchType.EAGER, cascade = CascadeType.ALL)
  @MapKey(name = "number")
  private Map<Integer, MethodContract> obligations;
}
