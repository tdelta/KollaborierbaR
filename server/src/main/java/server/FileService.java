package server;

import fr.loria.score.logootsplito.LogootSRopes;
import java.io.File;
import java.io.FileNotFoundException;
import java.util.NoSuchElementException;
import java.util.Scanner;
import java.util.concurrent.ConcurrentHashMap;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;
import synchronization.SynchronizationController;

@Service
public class FileService {

  @Autowired private SynchronizationController synchronizationController;

  /**
   * Get the current state of a collaborative document or if no one is currently working on the
   * document the state saved in the corresponding file
   *
   * @param filepath Path to the file including the project name e.g. /MyProject/src/test.txt
   */
  public String getCurrent(final String filepath) {
    ConcurrentHashMap<String, LogootSRopes> crdtDocs = synchronizationController.getDocuments();
    if (crdtDocs.containsKey(filepath)) {
      // Get the collaborative state of the document
      return crdtDocs.get(filepath).view();
    } else {
      // Load the document from disk
      return getSaved(filepath);
    }
  }

  /**
   * Load the contents of a text file
   *
   * @param filepath Path to the file including the project name e.g. /MyProject/src/test.txt
   */
  public String getSaved(final String filepath) {
    try {
      final String absolutePath = "projects/" + filepath;

      final File file = new File(absolutePath);

      final Scanner scan =
          new Scanner(/*scanners allow to read a file until a delimiter*/ file, "utf-8");

      // Check whether the requested file is empty
      if (!scan.hasNext()) {
        scan.close();
        return "";
      }

      final String content =
          scan.useDelimiter("\\Z").next(); // read until end of file (Z delimiter)
      // ^ using a scanner may not be optimal (could cause overhead),
      //  but simplifies this code so much, that we keep it for now

      scan.close();
      return content;

    } catch (FileNotFoundException e) {
      e.printStackTrace();
      System.out.println(
          "File could not be found. The following path was used for search:" + filepath);
      return "";
    } catch (NoSuchElementException e) {
      e.printStackTrace();
      System.out.println("Read Error. Error while reading the request file: " + filepath);
      return "";
    } catch (IllegalStateException e) {
      e.printStackTrace();
      System.out.println("Read Error. Error while reading the request file: " + filepath);
      return "";
    }
  }
}
