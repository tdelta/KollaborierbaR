package repository;

import org.springframework.data.repository.CrudRepository;
import org.springframework.stereotype.Repository;

/**
 * Interface to the database, can be autowired where needed.
 */
@Repository
public interface FileRepository extends CrudRepository<File, Long> {

  /**
   * Returns a file that has the given name. There is a constraint on the database
   * for file names to be unique
   *
   * @param name The file name
   */
  public File findByName(final String name);

  /**
   * @param name File name
   * @return True if a file with the given name exists in the database
   */
  public boolean existsByName(final String name);
}
