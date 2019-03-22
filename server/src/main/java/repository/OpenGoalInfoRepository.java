package repository;

import proofutil.OpenGoalInfo;

import org.springframework.data.repository.CrudRepository;
import org.springframework.stereotype.Repository;

@Repository
public interface OpenGoalInfoRepository extends CrudRepository<OpenGoalInfo, Long> {

}
