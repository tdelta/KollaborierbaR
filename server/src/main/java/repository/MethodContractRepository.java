package repository;

import org.springframework.data.repository.CrudRepository;
import org.springframework.stereotype.Repository;

import java.util.List;
import proofutil.ProofNode;

@Repository
public interface MethodContractRepository extends CrudRepository<MethodContract, Long>{

  public List<MethodContract> findByFileName(String fileName);

}
