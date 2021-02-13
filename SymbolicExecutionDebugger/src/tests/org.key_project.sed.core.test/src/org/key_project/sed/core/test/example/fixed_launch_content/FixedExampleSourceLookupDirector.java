/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.core.test.example.fixed_launch_content;

import org.eclipse.debug.core.sourcelookup.AbstractSourceLookupDirector;
import org.eclipse.debug.core.sourcelookup.ISourceLookupParticipant;

/**
 * Implementation of {@link AbstractSourceLookupDirector} for the
 * fixed example.
 * @author Martin Hentschel
 */
public class FixedExampleSourceLookupDirector extends AbstractSourceLookupDirector {
    /**
     * {@inheritDoc}
     */
    @Override
    public void initializeParticipants() {
        addParticipants(new ISourceLookupParticipant[] {new FixedExampleSourceLookupParticipant()});
    }
}