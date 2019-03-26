package repository;

import proofutil.OpenGoalInfo;

import org.springframework.data.repository.CrudRepository;
import org.springframework.stereotype.Repository;

/**
 * Interface to the database, can be autowired where needed.
 */
@Repository
public interface OpenGoalInfoRepository extends CrudRepository<OpenGoalInfo, Long> {

}
