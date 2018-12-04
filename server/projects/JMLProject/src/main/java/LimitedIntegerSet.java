import java.util.function.Consumer;

public class LimitedIntegerSet {

  //@ public invariant (\forall int i,j; i>=0 && i<j && j<size; arr[i] != arr[j]);
  private /*@ spec_public @*/ int[] arr;

  //@ public invariant size >= 0 && size <= arr.length;
  private /*@ spec_public @*/ int size;

  private void provokeWarning() {
    Consumer<Integer> noLambdaSupport = x -> {};

    switch (1) {
      case 1:
        System.out.println("Hello World");
      case 2: // There's a fall-through warning around here
        break;
    }
  }

  public LimitedIntegerSet(int limit) {
    this.arr = new int[limit];
  }


  /*@ public normal_behavior /// This is a JML comment.
    @ ensures \result == (\exists int i;
    @                             0 <= i && i < size;
    @                             arr[i] == elem);
    @*/
  public /*@ pure @*/ boolean contains(int elem) {/*...*/ throw new RuntimeException("Not yet implemented");}



  /*@ public normal_behavior
    @ requires contains(elem);
    @ assignable size, arr[*];  // allows arbitrary reordering of the array elements
    @ ensures !contains(elem); 
    @ ensures (\forall int e;
    @                  e != elem;
    @                  contains(e) <==> \old(contains(e)));
    @ ensures size == \old(size) - 1;
    @
    @ also
    @ 
    @ public normal_behavior
    @ requires !contains(elem);
    @ assignable \nothing;
    @*/
  public void remove(int elem) {/*...*/}


  // we specify that the array is sorted afterwards and that the set has not changed; the latter works in this case and is easier 
  // than if we would have to try to formalize permutation
  /*@ public normal_behavior
    @ assignable a[0..size - 1];
    @ ensures
    @   (\forall int i, j; i>=0 && i<j && j<size; arr[i]<arr[j]);
    @ ensures (\forall int e;  
    @                  contains(e) <==> \old(contains(e)));
    @*/
  public void sort() { /* ... */ }


  /*@ public normal_behavior
    @ requires size > 0;
    @ assignable \nothing;
    @ ensures ( \forall int i;
    @                  i>=0 && i<size;
    @                  \result >= a[i] );
    @ ensures ( \exists int i;
    @                  i>=0 && i<size;
    @                  \result == a[i] );
    @
    @ also
    @ 
    @ public exceptional_behavior
    @ requires size == 0;
    @ assignable \nothing;
    @ signals  (RuntimeException) true;
    @*/
  public int max() {
    // ...
    throw new RuntimeException("Not yet implemented.");
  }



}
