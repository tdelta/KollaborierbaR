public class Book {
  //@ public invariant 1 <= currentPage && currentPage <= lastPage; 
  private /*@ spec_public @*/ int currentPage;
  
  //@ public invariant lastPage >= 1; 
  private /*@ spec_public @*/ int lastPage;
  
  /*@ public invariant (\forall int i; i>=0 && i < bookmarks.length;  
                          (bookmarks[i] == 0 || (bookmarks[i] >= 1 && bookmarks[i]<=lastPage))); 
  @*/
  private /*@ spec_public @*/ int[] bookmarks = new int[10];

  
  /*@ public normal_behavior
    @ requires numberOfPages >= 1;
    @ assignable \nothing;
    @ ensures currentPage == 1 && lastPage == numberOfPages; 
    @*/
  public Book(int numberOfPages) { 
    this.currentPage = 1;
    this.lastPage = numberOfPages; 
  }

  /*@ public normal_behavior
    @ assignable \nothing;
    @ ensures \result == currentPage;
    @*/
  public int getCurrentPage() {
    return currentPage;
  }
  
  
  // the natural language specification does not provide details on where the bookmark is placed
  // the JML spec. does thus neither giving the implementor freedom
  // but as we cannot address the index directly the assignable clause allows too much and we need to 
  // narrow it down as part of the postcondition
  // Attention: This spec. is for the case where one page can have several bookmarks. How does one look where at most one
  // bookmark per page is allowed to exist? 
  /*@ public normal_behavior
    @ requires (\exists int i; i>=0 && i<bookmarks.length; bookmarks[i] == 0);
    @ assignable bookmarks[*];
    @ ensures (\exists int i; i>=0 && i<bookmarks.length; bookmarks[i] == currentPage && \old(bookmarks[i]) == 0 && 
    @     (\forall int j; j>=0 && j<bookmarks.length && j != i; bookmarks[j] == \old(bookmarks[j])));
    @     
    @ also 
    @
    @ public exceptional_behavior
    @ requires !(\exists int i; i>=0 && i<bookmarks.length; bookmarks[i] == 0);
    @ assignable \nothing;
    @ signals (RuntimeException) true;      
    @*/
  public void mark() { 
    // loop invariants will be explained in later lectures, 
      // for these exercises only the method level contracts were 
      // required
      /*@ loop_invariant i>=0 && i<=bookmarks.length &&
      @   (\forall int j; j>=0 && j<i; bookmarks[j] != 0);
      @ decreases bookmarks.length - i;
      @ assignable \nothing;
      @*/
    for (int i = 0; i<bookmarks.length; i++) {
      if (bookmarks[i] == 0) {
        bookmarks[i] = currentPage;
        return;
      }
    }
    throw new RuntimeException();	  
  }
}
