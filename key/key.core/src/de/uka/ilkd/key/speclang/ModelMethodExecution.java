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

package de.uka.ilkd.key.speclang;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.Pair;


public final class ModelMethodExecution extends ClassAxiom {

    private final String name;
    private final IObserverFunction target;
    private final KeYJavaType kjt;
    private final VisibilityModifier visibility;

    public ModelMethodExecution(String name,
                                IObserverFunction target,
                                KeYJavaType kjt,
                                VisibilityModifier visibility) {
        this(name,null,target,kjt,visibility);
    }

    public ModelMethodExecution(String name,
                                String displayName,
                                IObserverFunction target,
                                KeYJavaType kjt,
                                VisibilityModifier visibility) {

        assert name != null;
        assert kjt != null;
        assert target != null;
        this.name = name;
        this.target = target;
        this.kjt = kjt;
        this.visibility = visibility;
        this.displayName = displayName;
    }

    @Override
    public boolean equals(Object o) {
       if (o == null || this.getClass() != o.getClass()) return false;
       final ModelMethodExecution other = (ModelMethodExecution) o;
       
       if (!name.equals(other.name)) return false;
       if (!target.equals(other.target)) return false;
       if (!kjt.equals(other.kjt)) return false;
       
       return true;
    }
    
    @Override
    public int hashCode() {
       return 17*(name.hashCode() + 17 * target.hashCode());
    }
    
    @Override
    public ImmutableSet<Taclet> getTaclets(ImmutableSet<Pair<Sort, IObserverFunction>> toLimit, Services services) {

      // Name tacletName = MiscTools.toValidTacletName(name);
      //  TacletGenerator TG = TacletGenerator.getInstance();
        return null;
//            return TG.generateModelMethodExecutionTaclets(tacletName,
//                                                          kjt,
//                                                          target,
//                                                          services);
    }

    public ImmutableSet<Pair<Sort, IObserverFunction>> getUsedObservers(Services services) {
        return DefaultImmutableSet.<Pair<Sort, IObserverFunction>>nil();
    }

    public String getName() {
        return name;
    }

    public IObserverFunction getTarget() {
        return target;
    }

    public KeYJavaType getKJT() {
        return kjt;
    }

    public VisibilityModifier getVisibility() {
        return visibility;
    }

}