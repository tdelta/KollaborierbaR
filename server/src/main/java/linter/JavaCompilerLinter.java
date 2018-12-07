package linter;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import javax.tools.DiagnosticCollector;
import javax.tools.JavaCompiler;
import javax.tools.JavaCompiler.CompilationTask;
import javax.tools.JavaFileObject;
import javax.tools.ToolProvider;

import linter.Diagnostic;
import linter.JmlNotSupportedScanner;

import java.util.ArrayList;
import java.util.stream.Stream;

/**
 * Checks java source files for errors and warnings using the system java compiler (usually javac)
 * Also checks for features not supported by KeY.
 */
public class JavaCompilerLinter {
  final JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();

  /** Checks given source files for errors and returns diagnostics of all of them */
  public List<Diagnostic> check(final List<JavaFileObject> toCheck) {
    // Call respective helpers for compiler and KeY diagnostics.
    return Stream.concat(
        checkForCompilerErrors(toCheck).stream(),
        checkForUnsupportedFeatures(toCheck).stream()
    ).collect(Collectors.toList());
  }

  /**
   * Checks given source files for errors using the java compiler and returns
   * diagnostics of all of them.
   *
   * Example:
   * <pre> {@code
   *   checkForCompilerErrors(
   *     Arrays.asList(
   *       new JavaSourceMemoryObject("Main", "public class HelloWorld { ... }")
   *     )
   *   ) //will yield an ERROR diagnostic, that class name and file name do not match
   * }</pre>
   *
   * @param toCheck list of java source code files which shall be checked
   * @return        list of diagnostics, describing errors within the given files
   *                or empty list, if there are none
   */
  private List<Diagnostic> checkForCompilerErrors(final List<JavaFileObject> toCheck)
  {
    // this collector allows to capture diagnostic data regarding the source code errors
    final DiagnosticCollector<JavaFileObject> diagnosticsCollector =
        new DiagnosticCollector<JavaFileObject>();

    // setup compilation task
    final CompilationTask task =
        compiler.getTask(
            null, // no special output device, use System.err (will not be used, because of
                  // diagnostics listener)
            null, // use default file manager
            diagnosticsCollector, // collect diagnostics instead of usual compiler output
            Arrays.asList("-Xlint"), // enable all warnings
            null, // no class names for additional annotation processing
            toCheck // compile these files (can be located in memory,
                    // @see linting.linter.java.JavaMemoryFileObject)
            );

    // compile
    task.call(); // WARNING: Result (success status) currently ignored

    // return diagnostics
    List<Diagnostic> diagnostics = diagnosticsCollector
        .getDiagnostics()
        .stream()
        .map(
            JavaCompilerLinter
                ::normalizeDiagnostic) // convert java diagnostics representation to our format,
        // @see linting.linter.Diagnostics
        .collect(Collectors.toList());

    return diagnostics;
  }

  /**
   * Checks given source files for java features, which are not yet supported
   * by KeY using a custom JDT based checker.
   *
   * ATTENTION: For now, only the first file in the given list will be checked,
   * multiple files not supported yet!
   *
   * Example:
   * <pre> {@code
   *   checkForCompilerErrors(
   *     Arrays.asList(
   *       new JavaSourceMemoryObject("Main", "... float x = 3.1415; ...")
   *     )
   *   ) // will yield an NOT_SUPPORTED diagnostic, indicating, that KeY does
   *     // not support floats.
   * }</pre>
   *
   * @param toCheck list of java source code files which shall be checked
   * @return        list of diagnostics, describing not supported features within the given files
   *                or empty list, if there are none
   */
  private List<Diagnostic> checkForUnsupportedFeatures(final List<JavaFileObject> toCheck)
  {
    if (toCheck.size() > 0) {
      final JmlNotSupportedScanner scanner =
          new JmlNotSupportedScanner(toCheck.get(0));

      return scanner.run();
    }

    else {
      return new ArrayList<>(0);
    }
  }

  /**
   * Converts java diagnostics representation (@see javax.tools.Diagnostic) to a simplified
   * representation (@see linting.linter.Diagnostic).
   */
  private static Diagnostic normalizeDiagnostic(
      final javax.tools.Diagnostic<? extends JavaFileObject> d) {
    // determine the error type
    final Diagnostic.Kind kind;

    switch (d.getKind()) {
      case ERROR:
        kind = Diagnostic.Kind.ERROR;
        break;

      case WARNING:
        kind = Diagnostic.Kind.WARNING;
        break;

      default: // to simplify things, everything else is interpreted as NOTE
        kind = Diagnostic.Kind.NOTE;
    }

    return new Diagnostic(
        d.getMessage(null),
        d.getStartPosition(),
        d.getEndPosition(),
        d.getSource(),
        kind);
  }
}
