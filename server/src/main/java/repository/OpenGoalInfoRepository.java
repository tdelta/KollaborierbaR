package repository;

import org.springframework.data.repository.CrudRepository;
import org.springframework.stereotype.Repository;
import proofutil.OpenGoalInfo;

/** Interface to the database, can be autowired where needed. */
@Repository
public interface OpenGoalInfoRepository extends CrudRepository<OpenGoalInfo, Long> {}
