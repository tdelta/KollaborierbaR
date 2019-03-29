class Branches {
    /*@ public normal_behavior
      @ ensures \result == a + b;
      @*/
    public int weirdAdd(final int a, final int b) {
        if (b >= 0) {
            return a - b;
        }
        
        else {
            return a +(-b);
        }
    }
}