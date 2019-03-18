package repository;

import org.springframework.stereotype.Repository;
import org.springframework.data.repository.CrudRepository;
import proofutil.ObligationResult;

import java.util.List;

@Repository
public interface ObligationResultRepository extends CrudRepository<ObligationResult, Long> {
    public List<ObligationResult> findByMethodContractId(final long methodContractId);
}
