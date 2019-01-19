package synchronization.data;

import java.util.Arrays;
import java.util.stream.Collectors;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;

public class LogootSAdd extends fr.loria.score.logootsplito.LogootSAdd<Character> {

  private Identifier id;
  private String content;

  @JsonCreator
  public LogootSAdd(@JsonProperty("id") Identifier id,@JsonProperty("content") String content){
    super((fr.loria.score.logootsplito.Identifier) id,
        content.chars().mapToObj(c -> (char) c).collect(Collectors.toList()));

    this.id = id;
    this.content = content;
  }


  public String getContent(){
    return content;
  }

  public Identifier getId(){
    return id;
  }
}

