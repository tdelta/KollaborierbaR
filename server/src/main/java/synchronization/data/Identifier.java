package synchronization.data;

import java.util.LinkedList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.fasterxml.jackson.annotation.JsonIgnore;


public class Identifier extends fr.loria.score.logootsplito.Identifier {

  @JsonCreator
  public Identifier(@JsonProperty("tuples") IdentifierTuple[] tuples){
    super(Arrays.stream(tuples).flatMap(i -> Stream.of(i.random,i.replicaNumber,i.clock,i.offset))
        .limit(tuples.length*4-1).collect(Collectors.toList()),
        tuples[tuples.length-1].offset);
  }

  public IdentifierTuple[] getTuples(){
    if(getBase().size() < 3) return null;

    int numTuples = (int) Math.ceil(getBase().size()/4D); // round up
    IdentifierTuple[] tuples = new IdentifierTuple[numTuples];
    List<Integer> base = this.getBase();

    for(int i=0; i<numTuples-1; i++){
      int start = i*4;
      tuples[i] = new IdentifierTuple(base.get(start),base.get(start+1),
          base.get(start+2),base.get(start+3));
    }

    int last = (numTuples-1)*4;
    tuples[numTuples-1] = new IdentifierTuple(base.get(last),base.get(last+1),
        base.get(last+2),getLast());

    return tuples;
  }

  // Dont include this function of the superclass in the JSON output
  @Override
  @JsonIgnore
  public List<Integer> getBase() {
    return super.getBase();
  }

  // Dont include this function of the superclass in the JSON output
  @Override
  @JsonIgnore
  public Integer getLast() {
    return super.getLast();
  }
}
