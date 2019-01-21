package synchronization.data;

import java.util.List;

import com.fasterxml.jackson.annotation.JsonCreator;                                                                    
import com.fasterxml.jackson.annotation.JsonProperty;                                                                   

public class LogootSDel extends fr.loria.score.logootsplito.LogootSDel {

  @JsonCreator
  public LogootSDel(@JsonProperty("lid")List<IdentifierInterval> lid){
    super(lid);
  }
}
