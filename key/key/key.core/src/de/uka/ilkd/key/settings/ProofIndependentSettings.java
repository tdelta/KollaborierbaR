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

package de.uka.ilkd.key.settings;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.EventObject;
import java.util.Properties;

import de.uka.ilkd.key.pp.NotationInfo;



public class ProofIndependentSettings implements SettingsListener {
    public static final ProofIndependentSettings DEFAULT_INSTANCE =
            new ProofIndependentSettings(PathConfig.getProofIndependentSettings());
    private final ProofIndependentSMTSettings smtSettings =
            ProofIndependentSMTSettings.getDefaultSettingsData();
    private final LemmaGeneratorSettings lemmaGeneratorSettings =
            new LemmaGeneratorSettings();
    private final GeneralSettings generalSettings = new GeneralSettings();
    private final ViewSettings viewSettings = new ViewSettings();
    private final String filename;

    private final TestGenerationSettings testGenSettings = new TestGenerationSettings();

    private final Settings[] settingsSet =
        { smtSettings,
          lemmaGeneratorSettings,
          generalSettings,
          viewSettings,
          testGenSettings};



    private ProofIndependentSettings(String filename) {
        this.filename = filename;
        for (Settings settings : settingsSet) {
            settings.addSettingsListener(this);
        }
        loadSettings();
    }

    @Override
    public void settingsChanged(EventObject e) {
        saveSettings();

    }

    private void loadSettings() {
        try {
            File testFile = new File(filename);
            if(testFile.exists()) {
                if(Boolean.getBoolean(PathConfig.DISREGARD_SETTINGS_PROPERTY)) {
                    System.err.println("The settings in " +
                            filename + " are *not* read.");
                } else {
                    load(testFile);
                }
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private void load(File file) throws IOException {
        FileInputStream in = new FileInputStream(file);
        Properties properties = new Properties();
        properties.load(in);
        for(Settings settings : settingsSet) {
            settings.readSettings(this, properties);
        }
        in.close();
    }

    public void saveSettings() {

        try {
            File file = new File(filename);
            if (!file.exists()) {
                new File(PathConfig.getKeyConfigDir() + File.separator).mkdirs();
                file.createNewFile();
            }
            Properties result = new Properties();
            for (Settings settings : settingsSet) {
                settings.writeSettings(this, result);
            }
            FileOutputStream out = new FileOutputStream(file);
            try {
                result.store(out, "Proof-Independent-Settings-File");
            } finally {
                out.close();
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }

    }

    public GeneralSettings getGeneralSettings() {
        //ensureInitialized();
        return generalSettings;
    }

    public ViewSettings getViewSettings() {
        //ensureInitialized();
        return viewSettings;
    }
    public LemmaGeneratorSettings getLemmaGeneratorSettings() {
        return lemmaGeneratorSettings;
    }

    public ProofIndependentSMTSettings getSMTSettings() {
        return smtSettings;
    }

    public TestGenerationSettings getTestGenerationSettings() {
        return testGenSettings;
    }




    /**
     * Checks if pretty printing is enabled or not.
     * @return {@code true} pretty printing is enabled, {@code false} pretty printing is disabled.
     */
    public static boolean isUsePrettyPrinting() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
    }

    /**
     * Defines if pretty printing is enabled or not.
     * @param usePrettyPrinting {@code true} pretty printing is enabled,
     *     {@code false} pretty printing is disabled.
     */
    public static void setUsePrettyPrinting(boolean usePrettyPrinting) {
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUsePretty(usePrettyPrinting);
        NotationInfo.DEFAULT_PRETTY_SYNTAX = usePrettyPrinting;
    }
}