package linting.server;

import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.ResponseBody;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.RestController;
import org.springframework.web.bind.annotation.CrossOrigin;

import java.util.List;
import java.util.Arrays;

import linting.linter.Diagnostic;
import linting.linter.java.JavaCompilerLinter;
import linting.linter.java.JavaSourceMemoryObject;

/**
 * Naive HTTP API (RESTful?) for linting (java) source code
 */
@RestController
public class LinterController {
    private final JavaCompilerLinter linter = new JavaCompilerLinter();

    /**
     *  implements "/lint" routing
     *
     * @param name class name of java source file
     * @param source source code of file
     *
     * Example: POST request to http://myserver/lint?name=MyClass with the source code of MyClass.java
     * within the request body.
     */
    @RequestMapping("/lint")
    @ResponseBody
    @CrossOrigin
    public List<Diagnostic> lint(
          @RequestParam("name") String name,
          @RequestBody String source
        ) {
        return linter.check(
            Arrays.asList(new JavaSourceMemoryObject(name, source))
        );
    }
}
