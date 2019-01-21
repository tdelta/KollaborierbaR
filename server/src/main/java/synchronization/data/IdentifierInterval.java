package synchronization.data;

import java.util.List;

import com.fasterxml.jackson.annotation.JsonCreator;                                                                    
import com.fasterxml.jackson.annotation.JsonProperty;                                                                   
import com.fasterxml.jackson.annotation.JsonIgnore;

public class IdentifierInterval extends fr.loria.score.logootsplito.IdentifierInterval {

  private Identifier idBegin;

  @JsonCreator
  public IdentifierInterval(@JsonProperty("idBegin") Identifier idBegin,@JsonProperty("end") int end){
    super(idBegin.getBase(),idBegin.getLast(),end);
    this.idBegin = idBegin;
  }

  //public Identifier getIdBegin(){
  //  return idBegin;
  //}

  // Ignore all getters and setters of the superclass
  // Except for getEnd
  @Override
  @JsonIgnore
  public List<Integer> getBase() {
    return super.getBase();
  }

  @Override
  @JsonIgnore
  public fr.loria.score.logootsplito.Identifier getBeginId() {
    return super.getBeginId();
  }

  @Override
  @JsonIgnore
  public fr.loria.score.logootsplito.Identifier getEndId() {
    return super.getEndId();
  }

  @Override
  @JsonIgnore
  public int getBegin() {
    return super.getBegin();
  }

  @Override
  @JsonIgnore
  public fr.loria.score.logootsplito.Identifier getBaseId() {
    return super.getBaseId();
  }

  @Override
  @JsonIgnore
  public fr.loria.score.logootsplito.Identifier getBaseId(Integer u) {
    return super.getBaseId(u);
  }

  @Override
  @JsonIgnore
  public void setBegin(int begin) {
    super.setBegin(begin);
  }

  @Override
  @JsonIgnore
  public void setEnd(int end) {
    super.setEnd(end);
  }
} 
