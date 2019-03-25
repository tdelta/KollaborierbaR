import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.Matchers.allOf;
import static org.hamcrest.Matchers.hasItem;
import static org.hamcrest.beans.HasPropertyWithValue.hasProperty;
import static org.junit.Assert.assertThat;

import java.util.List;
import linter.Diagnostic;
import linter.JavaSourceMemoryObject;
import linter.JmlNotSupportedScanner;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.junit.Test;

/**
 * Tests implementation of linter, which checks java source code for java features, which are not
 * supported by KeY
 */
public class NotSupportedErrorsTest {
  private final String start = "public class Test{ public static void main(String[] args){\n";
  private final String end = "}}";

  /**
   * Tests if the JmlNotSupportedScanner returns the correct error when given a lambda expression
   */
  @Test
  public void testLambda() {
    final String source =
        "import java.util.function.Consumer;\n"
            + start
            + "Consumer<String> consumer = s -> {};"
            + end;

    JmlNotSupportedScanner subject =
        new JmlNotSupportedScanner(new JavaSourceMemoryObject("Test.java", source));
    CompilationUnit cu = createCompilationUnit(source, "Test.java");
    List<Diagnostic> results = subject.parseAst(cu);

    // Lint the source
    assertThat(
        "Correct error is returned for lambda expressions",
        results,
        hasItem(
            allOf(
                hasProperty("kind", is(Diagnostic.Kind.NOT_SUPPORTED)),
                hasProperty("message", is("Lambda expressions are not supported in KeY")),
                hasProperty("startRow", is(2L)))));
  }

  /**
   * Tests that no error is thrown when the scanner is called with no input and the result is empty
   */
  @Test
  public void testNoInput() {
    final String source = "";

    // Lint the source
    JmlNotSupportedScanner subject =
        new JmlNotSupportedScanner(new JavaSourceMemoryObject("Test.java", source));
    CompilationUnit cu = createCompilationUnit(source, "Test.java");
    List<Diagnostic> results = subject.parseAst(cu);

    assertThat("Scanning an empty source code yields no results", results.size(), is(0));
  }

  private CompilationUnit createCompilationUnit(String source, String name) {
    ASTParser parser = ASTParser.newParser(AST.JLS8);
    parser.setResolveBindings(true);
    try {
      parser.setSource(source.toCharArray());
    } catch (Exception e) {
      parser.setSource(new char[0]);
    }
    parser.setKind(ASTParser.K_COMPILATION_UNIT);
    parser.setBindingsRecovery(true);
    parser.setUnitName(name);

    final String[] sources = {"[~/TODO]"};
    final String[] classpath = {"[~/TODO]"};
    parser.setEnvironment(classpath, sources, new String[] {"UTF-8"}, true);

    final CompilationUnit cu = (CompilationUnit) parser.createAST(null);
    return cu;
  }
}
