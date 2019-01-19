package synchronization.data;

public class IdentifierTuple {

  public IdentifierTuple(int random, int replicaNumber,int clock, int offset){
    this.random = random;
    this.replicaNumber = replicaNumber;
    this.clock = clock;
    this.offset = offset;
  }

  public int random;
  public int replicaNumber;
  public int clock;
  public int offset;
}
