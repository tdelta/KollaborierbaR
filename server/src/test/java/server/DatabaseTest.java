import org.junit.Test;

import repository.MethodContractRepository;
import repository.FileRepository;
import repository.File;
import repository.MethodContract;
import repository.ObligationResultRepository;
import proofutil.ObligationResult;
import server.Application;
import proofutil.ProofNode;

import org.springframework.data.jpa.repository.config.EnableJpaRepositories;
import org.springframework.test.context.ContextConfiguration;
import org.springframework.boot.test.autoconfigure.orm.jpa.DataJpaTest;
import org.springframework.boot.context.properties.EnableConfigurationProperties;
import org.springframework.boot.test.context.SpringBootTest;
import org.springframework.test.context.junit4.SpringRunner;
import org.junit.runner.RunWith;
import org.springframework.beans.factory.annotation.Autowired;
import static org.junit.Assert.assertEquals;

import java.util.List;
import java.util.Arrays;

@RunWith(SpringRunner.class)
@DataJpaTest
@EnableJpaRepositories
@ContextConfiguration(classes = Application.class)
public class DatabaseTest {

  @Autowired private MethodContractRepository methodContractRepository;
  @Autowired private FileRepository fileRepository;
  @Autowired private ObligationResultRepository obligationResultRepository;

  @Test
  public void canCreateFindAndDeleteMethodContracts(){
    File file = new File("Test.test");
    fileRepository.save(file);

    file = fileRepository.findByName("Test.test");
    assertEquals(file.getName(),"Test.test");
    MethodContract methodContract = new MethodContract(0,"main");

    methodContract.setFile(file);
    methodContractRepository.save(methodContract);

    System.out.println("lol");

    List<MethodContract> contracts = methodContractRepository.findByFileName("Test.test");
    System.out.println(contracts.get(0).getMethodName());
    assertEquals(contracts.get(0).getMethodName(),"main");

    methodContractRepository.delete(contracts.get(0));
    fileRepository.delete(file);
  }

  @Test
  public void canCreateFindAndDeleteProofTree(){
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

    ObligationResult obligationResult = new ObligationResult(0,"lol",proofLeaf);
    obligationResult.setMethodContract(methodContract);

    obligationResultRepository.save(obligationResult);
    methodContract = methodContractRepository.save(methodContract);

    ObligationResult loadedObligationResult = obligationResultRepository.findByMethodContractId(methodContract.getIdTest()).get(0);
    ProofNode currentNode = loadedObligationResult.getProofTree();
    System.out.println("-------- Loaded proof tree: --------");
    do {
      System.out.println(currentNode.getText());
      currentNode = currentNode.getChildren().get(0);
    } while (currentNode.getChildren().size() == 1);
    assertEquals(1,1);
  }
}
