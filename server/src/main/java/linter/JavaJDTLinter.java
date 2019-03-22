package linter;

import java.io.IOException;
import java.util.Arrays;
import java.util.Hashtable;
import java.util.List;
import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.ToolProvider;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.compiler.IProblem;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.CompilationUnit;

/**
 * Checks java source files for errors and warnings using the eclipse jdt lib Also checks for
 * features not supported by KeY.
 */
public class JavaJDTLinter {
  final JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();

  /**
   * Checks given source files for errors using the eclipse jdt and returns diagnostics of all of
   * them.
   *
   * <p>Also checks for java features, which are not yet supported by KeY using a custom JDT based
   * checker.
   *
   * <p>ATTENTION: For now, only the first file in the given list will be checked, multiple files
   * not supported yet!
   *
   * <p>Examples:
   *
   * <pre>{@code
   * checkForCompilerErrors(
   *   Arrays.asList(
   *     new JavaSourceMemoryObject("Main", "public class HelloWorld { ... }")
   *   )
   * ) //will yield an ERROR diagnostic, that class name and file name do not match
   * }</pre>
   *
   * <pre>{@code
   * checkForCompilerErrors(
   *   Arrays.asList(
   *     new JavaSourceMemoryObject("Main", "... float x = 3.1415; ...")
   *   )
   * ) // will yield an NOT_SUPPORTED diagnostic, indicating, that KeY does
   *   // not support floats.
   * }</pre>
   *
   * @param toCheck list of java source code files which shall be checked
   * @return list of diagnostics, describing errors within the given files or empty list, if there
   *     are none
   */
  public List<Diagnostic> check(final List<JavaFileObject> toCheck) {
    // Create a syntax parser
    ASTParser parser = ASTParser.newParser(AST.JLS8);
    parser.setResolveBindings(true);
    try {
      parser.setSource(toCheck.get(0).getCharContent(true).toString().toCharArray());
    } catch (IOException e) {
      parser.setSource(new char[0]);
    }
    // Settings:
    // K_COMPIlATION_UNIT: Parse all expressions
    // Bindings recovery: Create bindings between variables and their content
    // Compiler options: For what to give errors
    // UnitName: File name
    parser.setKind(ASTParser.K_COMPILATION_UNIT);
    parser.setBindingsRecovery(true);
    parser.setCompilerOptions(getCompilerOptions());
    parser.setUnitName(toCheck.get(0).getName());

    // Compiler environment settings: from where to load resources
    final String[] sources = {"[~/TODO]"};
    final String[] classpath = {"[~/TODO]"};
    parser.setEnvironment(classpath, sources, new String[] {"UTF-8"}, true);

    // Create a syntax tree
    final CompilationUnit cu = (CompilationUnit) parser.createAST(null);
    final JmlNotSupportedScanner scanner = new JmlNotSupportedScanner(toCheck.get(0));

    // Get errors for not supported features
    List<Diagnostic> keyErrors = scanner.parseAst(cu);

    // Add all linter errors and warnings from jdt
    Arrays.asList(cu.getProblems()).stream()
        .map(problem -> normalizeDiagnostic(problem, toCheck.get(0)))
        .forEach(d -> keyErrors.add(d));

    return keyErrors;
  }

  /**
   * Converts java diagnostics representation (@see javax.tools.Diagnostic) to a simplified
   * representation (@see linting.linter.Diagnostic).
   */
  private static Diagnostic normalizeDiagnostic(final IProblem d, JavaFileObject source) {
    // determine the error type
    final Diagnostic.Kind kind;

    if (d.isError()) kind = Diagnostic.Kind.ERROR;
    else if (d.isWarning()) kind = Diagnostic.Kind.WARNING;
    else // to simplify things, everything else is interpreted as NOTE
    kind = Diagnostic.Kind.NOTE;

    return new Diagnostic(d.getMessage(), d.getSourceStart(), d.getSourceEnd() + 1, source, kind);
  }

  /**
   * This method creates compiler options that will be set in the ASTParser to generate errors and
   * warnings.
   *
   * @return A Hashtable containing the options
   */
  private Hashtable getCompilerOptions() {
    Hashtable options = JavaCore.getDefaultOptions();
    // Similar settings to javac -Xlint to recreate Xlint errors
    options.put(JavaCore.COMPILER_PB_FALLTHROUGH_CASE, JavaCore.WARNING);
    options.put(JavaCore.COMPILER_PB_AUTOBOXING, JavaCore.WARNING);
    options.put(JavaCore.COMPILER_PB_DEPRECATION, JavaCore.WARNING);
    options.put(JavaCore.COMPILER_PB_TERMINAL_DEPRECATION, JavaCore.WARNING);
    options.put(JavaCore.COMPILER_PB_ENUM_IDENTIFIER, JavaCore.WARNING);
    options.put(JavaCore.COMPILER_PB_FIELD_HIDING, JavaCore.WARNING);
    options.put(JavaCore.COMPILER_PB_FINALLY_BLOCK_NOT_COMPLETING, JavaCore.WARNING);
    options.put(JavaCore.COMPILER_PB_FORBIDDEN_REFERENCE, JavaCore.WARNING);
    options.put(JavaCore.COMPILER_PB_INCOMPATIBLE_NON_INHERITED_INTERFACE_METHOD, JavaCore.WARNING);
    options.put(JavaCore.COMPILER_PB_INCOMPLETE_ENUM_SWITCH, JavaCore.INFO);
    options.put(JavaCore.COMPILER_PB_LOCAL_VARIABLE_HIDING, JavaCore.WARNING);
    options.put(JavaCore.COMPILER_PB_MISSING_SERIAL_VERSION, JavaCore.WARNING);
    options.put(JavaCore.COMPILER_PB_NO_EFFECT_ASSIGNMENT, JavaCore.INFO);
    options.put(JavaCore.COMPILER_PB_NULL_REFERENCE, JavaCore.ERROR);
    options.put(JavaCore.COMPILER_PB_POSSIBLE_ACCIDENTAL_BOOLEAN_ASSIGNMENT, JavaCore.WARNING);
    options.put(JavaCore.COMPILER_PB_UNUSED_DECLARED_THROWN_EXCEPTION, JavaCore.WARNING);
    options.put(JavaCore.COMPILER_PB_UNUSED_PARAMETER, JavaCore.WARNING);
    // Set the java version to 1.8 so all features can be parsed
    options.put(JavaCore.COMPILER_SOURCE, JavaCore.VERSION_1_8);
    return options;
  }
}
