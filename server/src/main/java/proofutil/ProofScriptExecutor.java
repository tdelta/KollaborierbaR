package proofutil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Proof;
import java.io.IOException;
import java.util.Observer;

public class ProofScriptExecutor {

  private Proof proof;

  private DefaultUserInterfaceControl userInterfaceControl = new DefaultUserInterfaceControl();

  // TODO: send outputs to the client
  private Observer commandMonitor = (observable, object) -> {};

  /**
   * Executes a proof using a given macro. The result is saved in proofInput
   *
   * @param script the string contents of the macro file
   * @param proofInput the proof to work with
   */
  public void executeWithScript(final String script, Proof proofInput)
      throws IOException, InterruptedException, ScriptException {
    System.out.println("ProofScriptExecutor: Starting proof script");
    Location fileLocation = new Location("Proof script", 0, 0);

    ProofScriptEngine engine = new ProofScriptEngine(script, fileLocation);
    engine.setCommandMonitor(commandMonitor);
    engine.execute(userInterfaceControl, proofInput);
  }
}