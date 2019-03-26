package repository;

import org.springframework.data.repository.CrudRepository;
import org.springframework.stereotype.Repository;

import java.util.List;
import proofutil.ProofNode;

/**
 * Interface to the database, can be autowired where needed.
 */
@Repository
public interface MethodContractRepository extends CrudRepository<MethodContract, Long>{

  /**
   * Returns all method contracts that have a foreign key associated with a file with the given name
   *
   * @param fileName The name of the file
   */
  public List<MethodContract> findByFileName(String fileName);

}
