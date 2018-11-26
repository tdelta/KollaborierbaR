package linter;

import javax.annotation.processing.AbstractProcessor;
import java.util.LinkedList;
import linter.Diagnostic;
import javax.tools.JavaFileObject;
import javax.lang.model.element.Element;
import javax.lang.model.element.TypeElement;
import javax.annotation.processing.RoundEnvironment;
import javax.annotation.processing.ProcessingEnvironment;
import linter.JmlNotSupportedScanner;
import com.sun.source.util.Trees;
import java.util.Set;
import java.util.List;
import javax.annotation.processing.SupportedAnnotationTypes;


@SupportedAnnotationTypes("*")
public class JmlNotSupportedProcessor extends AbstractProcessor{
    // Unfortunately there is no default implementation of this class, since all it does is call the scanner
    private JmlNotSupportedScanner scanner;
    private Trees trees;
    private LinkedList<Diagnostic> results = new LinkedList<>();

    public JmlNotSupportedProcessor(JmlNotSupportedScanner scanner){
        this.scanner = scanner;
    }

    @Override
	public synchronized void init( final ProcessingEnvironment processingEnvironment ) {
        super.init( processingEnvironment );
        // Here we create a trees instance that makes it possible to extract the position of ast nodes in the source code
        trees = Trees.instance(processingEnvironment);
        results.clear();
    }

	public boolean process( final Set< ? extends TypeElement > types, final RoundEnvironment environment ) {
        if(!environment.processingOver()) {
            for( final Element element: environment.getRootElements() ) {
                scanner.setCompilationUnitTree(trees.getPath(element).getCompilationUnit());

                final List<Diagnostic> scanResults = scanner.scan(trees.getPath(element),trees);
                if(scanResults != null){
                    results.addAll(scanResults);
                }
            }
        }
        return true;
    }

    public LinkedList<Diagnostic> getResults(){
        return results;
    }
}
