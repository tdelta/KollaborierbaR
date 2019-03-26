package synchronization.data;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import java.util.stream.Collectors;

public class LogootSAdd extends fr.loria.score.logootsplito.LogootSAdd<Character> {

  private Identifier id;
  private String content;

  /**
   * @param id Identifier in the format of the mute-structs library
   * @param content The content of the removed or added text
   */
  @JsonCreator
  public LogootSAdd(@JsonProperty("id") Identifier id, @JsonProperty("content") String content) {
    super(
        (fr.loria.score.logootsplito.Identifier) id,
        content.chars().mapToObj(c -> (char) c).collect(Collectors.toList()));

    this.id = id;
    this.content = content;
  }

  public String getContent() {
    return content;
  }

  public Identifier getId() {
    return id;
  }
}
