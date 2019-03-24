package proofutil;

import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;

import java.io.IOException;
import java.lang.InterruptedException;
import java.util.Observer;

import de.uka.ilkd.key.macros.scripts.ScriptException;

public class ProofScriptExecutor{

    private Proof proof;    
    
    private DefaultUserInterfaceControl userInterfaceControl = new DefaultUserInterfaceControl(){
        @Override
        public void taskFinished(TaskFinishedInfo info) {
            proof = info.getProof();
        }
    };

    // TODO: send outputs to the client
    private Observer commandMonitor = (observable, object) -> {};

    public Proof executeWithScript(String script, Proof proofInput) throws IOException, InterruptedException, ScriptException{
        System.out.println("ProofScriptExecutor: Starting proof script");
        Location fileLocation = new Location("Proof script",0,0);
        
        ProofScriptEngine engine = new ProofScriptEngine(script,fileLocation);
        engine.setCommandMonitor(commandMonitor);
        engine.execute(userInterfaceControl, proofInput);
        return proof;
    }
}
