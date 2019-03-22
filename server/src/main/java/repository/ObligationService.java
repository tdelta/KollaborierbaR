package repository;

import repository.ObligationResultRepository;
import repository.MethodContractRepository;
import repository.FileRepository;
import repository.File;
import repository.MethodContract;
import proofutil.ObligationResult;
import proofutil.OpenGoalInfo;

import org.springframework.stereotype.Service;
import org.springframework.beans.factory.annotation.Autowired;

import javax.validation.ConstraintViolationException;
import java.util.Map;
import java.util.Optional;
import java.util.List;

@Service
public class ObligationService {
  

  @Autowired private ObligationResultRepository obligationResultRepository;
  @Autowired private MethodContractRepository methodContractRepository;
  @Autowired private FileRepository fileRepository;
  @Autowired private OpenGoalInfoRepository openGoalInfoRepository;

  public File getFile(String filename) {
    if(!fileRepository.existsByName(filename)) {
        File file = new File(filename);
        file = fileRepository.save(file);
        return file;
    } else {
        return fileRepository.findByName(filename);
    }
  }

  public MethodContract getMethodContract(File file, int obligationId){
    Map<Integer, MethodContract> contracts = file.getObligations();
    if(contracts.containsKey(obligationId)){
      return contracts.get(obligationId);
    } else {
      MethodContract methodContract = new MethodContract(obligationId);
      methodContract = methodContractRepository.save(methodContract);
      methodContract.setFile(file);
      methodContract = methodContractRepository.save(methodContract);
      return methodContract;
    }
  }

  public void deleteObligationResult(long id){
    obligationResultRepository.deleteById(id);
  }

  public Optional<ObligationResult> findObligationResultById(long id){
    return obligationResultRepository.findById(id);
  }

  public ObligationResult save(ObligationResult obligationResult){
    List<OpenGoalInfo> openGoals = obligationResult.getOpenGoals();
    if(openGoals != null){
        openGoals.stream()
          .map(openGoal -> openGoalInfoRepository.save(openGoal));
    }
    return obligationResultRepository.save(obligationResult);
  }

  public MethodContract save(MethodContract methodContract){
    return methodContractRepository.save(methodContract);
  }
}
