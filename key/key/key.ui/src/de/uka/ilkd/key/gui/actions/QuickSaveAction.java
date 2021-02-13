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

package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;

import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYConstants;

/**
 * Saves the current selected proof immediately to a temporaly location.
 * This feature can be conveniently accessed with the F5 key.
 * @author bruns
 */
public final class QuickSaveAction extends MainWindowAction {

    private static final long serialVersionUID = 8475988170848683884L;
    private static final File TMP_DIR = IOUtil.getTempDirectory();
    public static final String QUICK_SAVE_PATH = TMP_DIR+File.separator+".quicksave.key";

    public QuickSaveAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Quicksave");
//        setIcon(IconFactory.saveFile(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Save current proof to a temporal location.");

        mainWindow.getMediator().enableWhenProofLoaded(this);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        if (mainWindow.getMediator().ensureProofLoaded()) {
            final String filename = QUICK_SAVE_PATH;
            final Proof proof = mainWindow.getMediator().getSelectedProof();
            try {
                new ProofSaver(proof, filename, KeYConstants.INTERNAL_VERSION).save();
                final String status = "File quicksaved: "+filename;
                mainWindow.setStatusLine(status);
                Debug.out(status);
            } catch (IOException x) {
                mainWindow.popupWarning("Quicksaving file "+filename+" failed:\n"+x.getMessage(), "Quicksave failed");
                Debug.out("Quicksaving file "+filename+" failed.",x);
            }
        } else {
            mainWindow.popupWarning("No proof.", "Oops...");
        }
    }
}