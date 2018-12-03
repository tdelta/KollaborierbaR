package linter;

import javax.tools.JavaFileObject;

import java.util.List;
import java.util.LinkedList;
import java.io.IOException;

import linter.Diagnostic;

import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.PrimitiveType;
import org.eclipse.jdt.core.dom.ParameterizedType;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.MarkerAnnotation;
import org.eclipse.jdt.core.dom.NormalAnnotation;
import org.eclipse.jdt.core.dom.SingleMemberAnnotation;
import org.eclipse.jdt.core.dom.AssertStatement;
import org.eclipse.jdt.core.dom.TypeParameter;
import org.eclipse.jdt.core.dom.EnumDeclaration;
import org.eclipse.jdt.core.dom.EnumConstantDeclaration;
import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.Annotation;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.ImportDeclaration;
import org.eclipse.jdt.core.dom.NumberLiteral;
import org.eclipse.jdt.core.dom.TryStatement;
import org.eclipse.jdt.core.dom.CatchClause;
import org.eclipse.jdt.core.dom.TypeLiteral;
import org.eclipse.jdt.core.dom.SimpleType;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.LambdaExpression;

/**
 * Searches the AST of the given `sourceFile` for features not supported by
 * KeY. (It implements the visitor pattern.)
 *
 * Produces a list of diagnostic information about discovered issues.
 */
public class JmlNotSupportedScanner extends ASTVisitor {
    private final LinkedList<Diagnostic> results = new LinkedList<Diagnostic>();

    private final JavaFileObject sourceFile;
    private final char[] sourceCode;

    public JmlNotSupportedScanner(JavaFileObject sourceFile){
        this.sourceFile = sourceFile;

        char[] sourceCodeInitVar = null;

        try {
            // Extract the source code of the given JavaFileObject as String
            // and save it as a char array, such that it can be passed to the
            // JDT AST parser later on
            sourceCodeInitVar = sourceFile
              .getCharContent(true)
              .toString()
              .toCharArray();
        } catch(IOException e) {
            e.printStackTrace();
            sourceCodeInitVar = new char[0];
        }

        this.sourceCode = sourceCodeInitVar;
    }

    /**
     * Create a diagnostics object indicating the use of a feature not
     * supported by KeY at the given ASTNode.
     *
     * It will be saved in an internal list to be retrieved later within
     * run().
     *
     * @param node the node where the error was found (used to calculate the position of the error)
     * @param message a message to include in the error
     * @return a diagnostic object of the type NOT_SUPPORTED, containing the error message and the position of the AST node in the source code
     */
    private void saveDiagnostic(ASTNode node, String message){
        final int startPos = node.getStartPosition();
        final int endPos = startPos + node.getLength();

        results.add(new Diagnostic(
            message,
            startPos,
            endPos,
            sourceFile,
            Diagnostic.Kind.NOT_SUPPORTED));
    }

    /**
     * All visit methods work the same.
     * 
     * They are called when the parser finds a node of the type specified by the parameter
     * and create an error for unsupported features
     * 
     * @param node the node found by the AST parser
     * @return true if the children of this node should still be parsed
     */
    @Override
    public boolean visit(LambdaExpression node){
        saveDiagnostic(node,"Lambda expressions are not supported in KeY");
        return true;
    }

    @Override
    public boolean visit(PrimitiveType node){
        final String code = node.getPrimitiveTypeCode().toString();
        
        switch(code){
            case "float":
                saveDiagnostic(node,"Floats are not supported in KeY");
                break;
            case "double":
                saveDiagnostic(node,"Doubles are not supported in KeY");
                break;
        }
        return true;
    }

    @Override
    public boolean visit(AssertStatement node){
        saveDiagnostic(node,"Assert is not supported in KeY");
        return true;
    }

    @Override
    public boolean visit(ParameterizedType node){
        saveDiagnostic(node,"Generics are not suppported in KeY");
        return true;
    }

    @Override
    public boolean visit(TypeParameter node){
        saveDiagnostic(node,"Generics are not supported in KeY");
        return true;
    }
    
    @Override
    public boolean visit(NormalAnnotation node){
        return visitAnnotation(node);
    }

    @Override
    public boolean visit(MarkerAnnotation node){
        return visitAnnotation(node);
    }

    @Override
    public boolean visit(SingleMemberAnnotation node){
        return visitAnnotation(node);
    }

    public boolean visitAnnotation(Annotation node){
        saveDiagnostic(node,"Annotations are not supported in KeY");
        return true;
    }

    @Override
    public boolean visit(EnumDeclaration node){
        saveDiagnostic(node,"Enums are not supported in KeY");
        return true;
    }

    @Override
    public boolean visit(SingleVariableDeclaration node){
        if(node.isVarargs()) {
            saveDiagnostic(node,"Varargs are not supported in KeY");
        }

        return true;
    }

    @Override
    public boolean visit(EnumConstantDeclaration node){
        // TODO: Not working
        saveDiagnostic(node,"Enums are not supported in KeY");
        return true;
    }

    @Override
    public boolean visit(ImportDeclaration node){
        if(node.isStatic()) {
            saveDiagnostic(node,"Static imports are not supported in KeY");
        }

        return true;
    }
    
    @Override
    public boolean visit(NumberLiteral node){
        // TODO: Not working
        if(node.getToken().indexOf('b')>=0) {
            saveDiagnostic(node,"Binary literals are not supported in KeY");
        }

        return true;
    }

    @Override
    public boolean visit(TryStatement node){
        if(node.resources().size()!=0) {
            saveDiagnostic(node,"Try with resources is not supported in KeY");
        }

        final List<CatchClause> catchClauses = node.catchClauses();
        if(catchClauses.size() > 1){
            for(final CatchClause catchClause: catchClauses) {
                saveDiagnostic(catchClause,"Multiple catch clauses are not supported in KeY");
            }
        }
        return true;
    }

    @Override
    public boolean visit(SimpleType node){
        final String type = node.getName().getFullyQualifiedName();
        String message = "";

        switch(type){
            case "Runnable":
            case "Thread":
                message = "Multithreading is not supported in KeY";
                break;
        }

        if(message != "") {
            saveDiagnostic(node,message);
        }

        return true;
    }

    // TODO: Imported classes that implement runnable or Thread
    // TODO: Does KeY support Autoboxing?

    /**
     * Creates and parses an AST from the source code.
     *
     * @return A list of Diagnostics, containing all features that are not supported by key with their respective positions in the source code
     */
    public List<Diagnostic> run(){
        // Create AST from source code
        final ASTParser parser = ASTParser.newParser(AST.JLS8);

        parser.setSource(sourceCode);
        parser.setKind(ASTParser.K_COMPILATION_UNIT);

        final CompilationUnit cu = (CompilationUnit) parser
            .createAST(null); // null means, we dont want to install a progress monitor object
        // Apply the visitor on the created tree (visit methods above will be called on the nodes)
        cu.accept(this);

        return results;
    }
}
