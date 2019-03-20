package synchronization;

import repository.MethodContractRepository;
import repository.MethodContract;
import repository.ObligationResultRepository;
import repository.File;
import repository.FileRepository;
import proofutil.ObligationResult;
import proofutil.ProofNode;
import java.util.Arrays;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;
import org.springframework.context.event.EventListener;
import org.springframework.boot.context.event.ApplicationReadyEvent;
import org.springframework.data.jpa.repository.config.EnableJpaRepositories;

@Service
@EnableJpaRepositories("repository")
public class DatabaseTest {

  @Autowired private ObligationResultRepository obligationResultRepository;
  @Autowired private MethodContractRepository methodContractRepository;
  @Autowired private FileRepository fileRepository; 

  @EventListener(ApplicationReadyEvent.class)
  public void databaseOperations() {
    System.out.println("---------- Database test started ----------");

    File file = new File("Test.test");
    fileRepository.save(file);
    MethodContract methodContract = new MethodContract(0,"main");
    methodContract.setFile(file);
    methodContract = methodContractRepository.save(methodContract);

    ProofNode proofLeaf = new ProofNode(
        "node 2",
        Arrays.asList(new ProofNode[0]),
        ProofNode.Kind.DefaultNode,
        "lol",
        0,
        0
    );
    ProofNode proofTree = new ProofNode(
        "node 1",
        Arrays.asList(new ProofNode[]{proofLeaf}),
        ProofNode.Kind.DefaultNode,
        "lol",
        0,
        0
    );

    ObligationResult obligationResult = new ObligationResult(0,"lol",proofTree);
    obligationResult.setMethodContract(methodContract);

    obligationResultRepository.save(obligationResult);
    methodContract = methodContractRepository.findByFileName("Test.test").get(0);
    ObligationResult loadedObligationResult = obligationResultRepository.findByMethodContractId(methodContract.getIdTest()).get(0);
    System.out.println(loadedObligationResult.getProofTree().getText());
    System.out.println(loadedObligationResult.getProofTree().getChildren().get(0).getText());
  }
}
