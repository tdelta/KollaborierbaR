package synchronization.data;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import java.util.List;

public class LogootSDel extends fr.loria.score.logootsplito.LogootSDel {

  @JsonCreator
  public LogootSDel(@JsonProperty("lid") List<IdentifierInterval> lid) {
    super(lid);
  }
}
