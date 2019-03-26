package repository;

import org.springframework.stereotype.Repository;
import org.springframework.data.repository.CrudRepository;
import proofutil.ObligationResult;

import java.util.List;

/**
 * Interface to the database, can be autowired where needed.
 */
@Repository
public interface ObligationResultRepository extends CrudRepository<ObligationResult, Long> {

  /**
   * Returns all obligation results that have a foreign key associated with a specific method contract
   *
   * @param methodContractId primary key of the method contract
   */
  public List<ObligationResult> findByMethodContractId(final long methodContractId);
}
