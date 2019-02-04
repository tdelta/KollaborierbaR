package server;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import linter.Diagnostic;
import linter.JavaJDTLinter;
import linter.JavaSourceMemoryObject;
import org.springframework.web.bind.annotation.CrossOrigin;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.ResponseBody;
import org.springframework.web.bind.annotation.RestController;

/** Naive HTTP API (RESTful?) for linting (java) source code */
@RestController
public class LinterController {
  private final JavaJDTLinter linter = new JavaJDTLinter();

  /**
   * implements "/lint" routing
   *
   * @param name class name of java source file
   * @param source source code of file
   *     <p>Example: POST request to http://myserver/lint?name=MyClass with the source code of
   *     MyClass.java within the request body.
   */
  @RequestMapping("/lint")
  @ResponseBody
  @CrossOrigin
  public List<Diagnostic> lint(
      @RequestParam("name") String filename, @RequestBody(required = false) String source) {
    // check, whether there is a body
    if (source != null) {
      // Cut away .java of the file name for the java compiler
      final String classname = cutFileExtension(filename);

      try {
        return linter.check(Arrays.asList(new JavaSourceMemoryObject(classname, source)));
      } catch (final Exception e) {
        e.printStackTrace();

        // TODO proper error handling
        return new ArrayList<>(0);
      }
    } else {
      return new ArrayList<>(0);
    }
  }

  /**
   * Method cuts of the .java file extension of a string, if .java is at the end of the string
   *
   * @param filename of the file, for which the extension should be cut off
   * @return name without the file extension
   * @example cutFileExtension("Main.java") == "Main" cutFileExtension("LoremIpsum") == "LoremIpsum"
   */
  private String cutFileExtension(final String filename) {
    String classname = filename;

    // Length of the name is necessary
    final int length = filename.length();

    // If length is too small, it is not possible that there is an .java at the end
    if (length < 5) {
      classname = filename;
    } else {
      // String that might contain the file extension
      final String fileextension = filename.substring(length - 5);

      // If last 5 chars of string match .java, cut off the last 5 chars
      if (fileextension.equals(".java")) {
        classname = filename.substring(0, length - 5);
      }
    }

    return classname;
  }
}
