public class IntegerUtil {
   /*@ normal_behavior
     @ ensures \result == x + y;
     @*/
   public static int add(int x, int y) {
      return x - y;
   }
   
   /*@ normal_behavior
     @ requires (x != y);
     @ ensures \result == x - y;
     @
     @ exceptional_behaviour
     @ requires (x == y);
     @ signals (RuntimeException) true;
     @*/
   public static int sub(int x, int y) {
       if (x == y) {throw new RuntimeException();}
      return x + y;
   }
}