package linting.linter.java;

import javax.tools.DiagnosticCollector;
import javax.tools.JavaCompiler;
import javax.tools.JavaCompiler.CompilationTask;
import javax.tools.JavaFileObject;
import javax.tools.ToolProvider;

import java.util.List;
import java.util.stream.Collectors;

import linting.linter.Diagnostic;

/**
 * Checks java source files for errors and warnings using the system java compiler (usually javac)
 */
public class JavaCompilerLinter {
  final JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();

  /**
   * Checks given source files for errors and returns diagnostics of all of them
   */
  public List<Diagnostic> check(final List<JavaFileObject> toCheck) {
    // this collector allows to capture diagnostic data regarding the source code errors
    final DiagnosticCollector<JavaFileObject> diagnosticsCollector = new DiagnosticCollector<JavaFileObject>();

    // setup compilation task
    final CompilationTask task = compiler.getTask(
        null, // no special output device, use System.err (will not be used, because of diagnostics listener)
        null, // use default file manager
        diagnosticsCollector, // collect diagnostics instead of usual compiler output
        null, // no compiler options
        null, // no class names for additional annotation processing
        toCheck // compile these files (can be located in memory, @see linting.linter.java.JavaMemoryFileObject)
    );

    // compile
    task.call(); //WARNING: Result (success status) currently ignored

    // return diagnostics
    return diagnosticsCollector
      .getDiagnostics()
      .stream()
      .map(JavaCompilerLinter::normalizeDiagnostic) // convert java diagnostics representation to our format, @see linting.linter.Diagnostics
      .collect(Collectors.toList());
  }

  /**
   * Converts java diagnostics representation (@see javax.tools.Diagnostic) to
   * a simplified representation (@see linting.linter.Diagnostic).
   */
  private static Diagnostic normalizeDiagnostic(final javax.tools.Diagnostic<? extends JavaFileObject> d) {
    //determine the error type
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
        d.getColumnNumber(),
        d.getLineNumber(),
        d.getStartPosition(),
        d.getEndPosition(),
        d.getPosition(),
        kind
    );
  }
}

