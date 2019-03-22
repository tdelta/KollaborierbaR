package repository;

import org.springframework.data.repository.CrudRepository;
import org.springframework.stereotype.Repository;

@Repository
public interface FileRepository extends CrudRepository<File, Long> {

  public File findByName(final String name);

  public boolean existsByName(final String name);
}
