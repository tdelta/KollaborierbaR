import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.Matchers.contains;
import static org.hamcrest.Matchers.hasItem;
import static org.hamcrest.Matchers.allOf;
import static org.hamcrest.beans.HasPropertyWithValue.hasProperty;
import static org.junit.Assert.assertThat;
import org.junit.Test;

import linter.JmlNotSupportedScanner;
import linter.JavaSourceMemoryObject;
import linter.Diagnostic;
import java.util.List;

/**
 * Tests implementation of linter, which checks java source code for java
 * features, which are not supported by KeY
*/
public class NotSupportedErrorsTest{
    private final String start = "public class Test{ public static void main(String[] args){\n";
    private final String end = "}}";

    /**
     * Tests if the JmlNotSupportedScanner returns the correct error when given a lambda expression
     */
    @Test
    public void testLambda(){
        final String source =
            "import java.util.function.Consumer;\n"+
            start+
            "Consumer<String> consumer = s -> {};"+
            end;

        final JmlNotSupportedScanner subject =
            new JmlNotSupportedScanner(
                new JavaSourceMemoryObject("Test.java", source)
            );

        final List<Diagnostic> results = subject.run();

        // Lint the source
        assertThat(
            "Correct error is returned for lambda expressions",
            results,
            hasItem(
                allOf(
                    hasProperty("kind", is(Diagnostic.Kind.NOT_SUPPORTED)),
                    hasProperty("message", is("Lambda expressions are not supported in KeY")),
                    hasProperty("startRow", is(2L))
                )
        ));
    }

    /**
     * Tests that no error is thrown when the scanner is called with no input and the result is empty
     */
    @Test
    public void testNoInput(){
        final String source = "";

        // Lint the source
        final JmlNotSupportedScanner subject = new JmlNotSupportedScanner(
            new JavaSourceMemoryObject("Test.java",source)
        );
        final List<Diagnostic> results = subject.run();
        
        assertThat(
            "Scanning an empty source code yields no results",
            results.size(),
            is(0));
    }
}
