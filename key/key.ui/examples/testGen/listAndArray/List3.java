/*This is a test generation example for the KeYToolPaper2014. Both methods (get and l2a) satisfy the specification.
  Author: Christoph Gladisch
*/

class List3 {
/*@ nullable */ public List3 nxt;
 
/*@ public normal_behaviour
 ensures (i==0 ==> \result==this) &&
 ((nxt==null || i<0) && i!=0 ==> \result==null) &&
 (i>0 && nxt!=null ==> \result==nxt.get(i-1)); @*/ 
public /*@ pure nullable */ List3 get(int i){
 if(i==0) return this;
 return (nxt==null || i<0)? null:nxt.get(i-1);
}

/*@ public normal_behaviour
requires a.length>0 && l!=null;
ensures (\forall int i;1<=i && i<a.length; 
                        a[i] == l.get(i));@*/ 
public void l2a(/*@nullable */List3 l, List3[] a){            
   for(int i = 0; i< a.length; i++){
      a[i]=l;
      if(l!=null){ l=l.nxt;}
   }
} }
