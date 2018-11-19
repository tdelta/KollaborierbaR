package linting.linter.java;

import java.net.URI;
import javax.tools.SimpleJavaFileObject;

/** Stores java source code in memory */
public class JavaSourceMemoryObject extends SimpleJavaFileObject {
  final String code;

  /**
   * @param pname class name (with package path) e.g. a.b.MyClass
   * @param code source code of file
   */
  public JavaSourceMemoryObject(String pname, String code) {
    super(
        URI.create(
            // convert package path to file path and add java source code extension
            "string:///" + pname.replace('.', '/') + Kind.SOURCE.extension),
        Kind.SOURCE);

    this.code = code;
  }

  @Override
  public CharSequence getCharContent(boolean ignoreEncodingErrors) {
    return code;
  }
}
