package server;

import java.util.Arrays;
import java.util.List;
import linter.Diagnostic;
import linter.java.JavaCompilerLinter;
import linter.java.JavaSourceMemoryObject;
import org.springframework.web.bind.annotation.CrossOrigin;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.ResponseBody;
import org.springframework.web.bind.annotation.RestController;

/** Naive HTTP API (RESTful?) for linting (java) source code */
@RestController
public class LinterController {
  private final JavaCompilerLinter linter = new JavaCompilerLinter();

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
  public List<Diagnostic> lint(@RequestParam("name") String name, @RequestBody String source) {
	  
	  // Cut away .java of the file name for the java compiler
	  name = cutFileExtension(name);
	  
	  return linter.check(Arrays.asList(new JavaSourceMemoryObject(name, source)));
  }
  
  
  /**
   * 
   * Method cuts of the .java file extension of a string, if .java is at the end of the string
   * 
   * @param name of the file, for which the extension should be cut off
   * @return name without the file extension
   */
  private String cutFileExtension(String name) {
	
	  // Length of the name is necessary 
	  int length = name.length();
	  
	  // If length is to small, it is not possible that there is an .java at the end
	  if(length < 5) {
		  return name;
	  }
	  
	  // String that maybe contains the fileextension
	  final String fileextension = name.substring(length-5);
	  
	  // If last 5 chars of string match .java, cut off the last 5 chars
	  if(fileextension.equals(".java")) {
		
		  name = name.substring(0, length-5);
		  
	  }
	  return name;
  } 
}
