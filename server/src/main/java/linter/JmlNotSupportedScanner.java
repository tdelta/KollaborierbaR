package linter;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.LambdaExpression;
import javax.tools.JavaFileObject;
import java.util.List;
import java.util.LinkedList;
import java.io.IOException;
import linter.Diagnostic;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.CompilationUnit;

public class JmlNotSupportedScanner extends ASTVisitor{

private LinkedList<Diagnostic> results = new LinkedList<Diagnostic>();

    private JavaFileObject sourceFile;
    private char[] sourceCode;

    public JmlNotSupportedScanner(JavaFileObject sourceFile){
        this.sourceFile = sourceFile;
        try{
        sourceCode = sourceFile.getCharContent(true).toString().toCharArray();
        } catch(IOException e) {
            e.printStackTrace();
            sourceCode = new char[0];
        }
    }

    @Override
    public boolean visit(LambdaExpression node){
        int startPos = node.getStartPosition();
        int endPos = startPos + node.getLength();
        results.add(new Diagnostic(
            "Lambda expressions are not supported in key",
            startPos,
            endPos,
            sourceFile,
            Diagnostic.Kind.ERROR));
        return true;
    }

    public List<Diagnostic> getResults(){
        // Create AST from source code
        ASTParser parser = ASTParser.newParser(AST.JLS8);
        parser.setSource(sourceCode);
        parser.setKind(ASTParser.K_COMPILATION_UNIT);
        final CompilationUnit cu = (CompilationUnit) parser.createAST(null);
        // Apply the visitor on the created tree (visit methods above will be called on the nodes)
        cu.accept(this);
        return results;
    }
}
