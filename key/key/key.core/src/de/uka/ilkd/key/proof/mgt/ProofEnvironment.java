// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.mgt;

import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/** The unique environment a proof is performed in. The environment
 * consists of a java model, specifications, and a set of justified
 * rules. Since the starting point of the proofs contained in the
 * environment is equal, there is an InitConfig contained to be used
 * to start proofs of this environment.
 */
public class ProofEnvironment {

   private final InitConfig initConfig; 
   private final Set<ProofAggregate> proofs = new LinkedHashSet<ProofAggregate>(); //of ProofList

   private final List<ProofEnvironmentListener> listeners = new LinkedList<ProofEnvironmentListener>();
   
   /** constructs a proof environment with the given initial
    * configuration of the proofs contained in the environment.
    */
   public ProofEnvironment(InitConfig initConfig) {
      this.initConfig = initConfig;
   }


   /** retrieves the java model underlying this environment.
    */
   public JavaModel getJavaModel() {
      return initConfig.getServices().getJavaModel();
   }


   /**
    * returns the {@link Services} instance for the environment
    * 
    * @return the {@link Services} instance for the environment
    */
   public Services getServicesForEnvironment() {
      return initConfig.getServices();
   }


   /** returns the initial configuration of which a copy can be
    * used to load proofs belonging to this environment. 
    */
   public InitConfig getInitConfigForEnvironment() {
      return initConfig;
   }

   /** registers a proof loaded with the given {@link 
    * de.uka.ilkd.key.proof.init.ProofOblInput}. The method adds
    * the proof list generated by the input to the suitable contract if one 
    * is found. In all cases the proof is added to the proofs of this 
    * environment and the proofs are marked to belong to this environment.
    */
   public void registerProof(ProofOblInput po, ProofAggregate pl) {
      pl.setProofEnv(this);
      proofs.add(pl);
      for(Proof p : pl.getProofs()) {
         getServicesForEnvironment().getSpecificationRepository().registerProof(po, p);
      }
      fireProofRegistered(new ProofEnvironmentEvent(this, po, pl));
   }
   
   public void addProofEnvironmentListener(ProofEnvironmentListener l) {
      if (l != null) {
         listeners.add(l);
      }
   }
   
   public void removeProofEnvironmentListener(ProofEnvironmentListener l) {
      if (l != null) {
         listeners.remove(l);
      }
   }
   
   public ProofEnvironmentListener[] getProofEnvironmentListeners() {
      return listeners.toArray(new ProofEnvironmentListener[listeners.size()]);
   }

   protected void fireProofRegistered(ProofEnvironmentEvent e) {
      for (ProofEnvironmentListener l : getProofEnvironmentListeners()) {
         l.proofRegistered(e);
      }
   }

   protected void fireProofUnregistered(ProofEnvironmentEvent e) {
      for (ProofEnvironmentListener l : getProofEnvironmentListeners()) {
         l.proofUnregistered(e);
      }
   }

   /** retrieves all proofs registered at this environment 
    */
   public Set<ProofAggregate> getProofs() {
      return proofs;
   }

   public void removeProofList(ProofAggregate pl) {
      proofs.remove(pl);
      
      //TODO: the above line should be enough
      for (ProofAggregate paChild : pl.getChildren()) {
         proofs.remove(paChild);
      }
      // 
      
      for(Proof p : pl.getProofs()) {
         getServicesForEnvironment().getSpecificationRepository()
         .removeProof(p);
      }
      
      fireProofUnregistered(new ProofEnvironmentEvent(this, null, pl));
   }


   /** returns true iff the java model equals those of the argument
    * proof environment. TODO: extend to available rules and specs.
    */
   public boolean equals(Object cmp) {
      if (!(cmp instanceof ProofEnvironment)) {
         return false;
      }
      ProofEnvironment pe = (ProofEnvironment) cmp;
      return pe.getJavaModel().equals(getJavaModel()) &&
            pe.initConfig.getActivatedChoices().equals(initConfig.getActivatedChoices());
   }

   public int hashCode() {
      int result = 5;
      result = result*17+ getJavaModel().hashCode();
      result = result*17+ initConfig.getActivatedChoices().hashCode();
      return result;
   }

   /** returns a short String description of the environment.
    */
   public String description() {
      return "Env. with "+getJavaModel().description();
   }

   public String toString() {
      return description();
   }    
}