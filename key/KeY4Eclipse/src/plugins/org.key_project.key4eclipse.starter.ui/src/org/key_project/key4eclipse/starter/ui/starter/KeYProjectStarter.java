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

package org.key_project.key4eclipse.starter.ui.starter;

import org.eclipse.core.resources.IProject;
import org.key_project.key4eclipse.common.ui.starter.IProjectStarter;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;

/**
 * Starts a proof in the original user interface of KeY.
 * @author Martin Hentschel
 */
public class KeYProjectStarter implements IProjectStarter {
   /**
    * {@inheritDoc}
    */
   @Override
   public void open(IProject project) throws Exception {
      KeYUtil.loadAsync(project);
   }
}