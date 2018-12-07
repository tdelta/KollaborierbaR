package linter;

import java.util.Arrays;
import org.eclipse.jdt.core.compiler.IProblem;
import org.eclipse.jdt.core.JavaCore;
import java.util.stream.Collectors;
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
import org.eclipse.jdt.core.dom.VariableDeclarationExpression;
import org.eclipse.jdt.core.dom.ArrayInitializer;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.VariableDeclarationExpression;
import org.eclipse.jdt.core.dom.ITypeBinding;

public class JmlNotSupportedScanner extends ASTVisitor{

    private LinkedList<Diagnostic> results = new LinkedList<Diagnostic>();

    private JavaFileObject sourceFile;

    public JmlNotSupportedScanner(JavaFileObject sourceFile){
        this.sourceFile = sourceFile;
    }

    /**
     * @param node the node where the error was found (used to calculate the position of the error)
     * @param message a message to include in the error
     * @return a diagnostic object of the type NOT_SUPPORTED, containing the error message and the position of the AST node in the source code
     */
    private void createError(ASTNode node,String message){
        int startPos = node.getStartPosition();
        int endPos = startPos + node.getLength();
        results.add(new Diagnostic(
            message,
            startPos,
            endPos,
            sourceFile,
            Diagnostic.Kind.NOT_SUPPORTED));
    }

    /**
     * All visit methods work the same. They are called when the parser finds a node of the type specified by the parameter
     * and create an error for unsupported features
     * @param node the node found by the AST parser
     * @return true if the children of this node should still be parsed
     */
    @Override
    public boolean visit(LambdaExpression node){
        createError(node,"Lambda expressions are not supported in KeY");
        return true;
    }

    @Override
    public boolean visit(PrimitiveType node){
        String code = node.getPrimitiveTypeCode().toString();
        switch(code){
            case "float":
                createError(node,"Floats are not supported in KeY");
                break;
            case "double":
                createError(node,"Doubles are not supported in KeY");
                break;
        }
        return true;
    }

    @Override
    public boolean visit(AssertStatement node){
        createError(node,"Assert is not supported in KeY");
        return true;
    }

    @Override
    public boolean visit(ParameterizedType node){
        createError(node,"Generics are not suppported in KeY");
        return true;
    }

    @Override
    public boolean visit(TypeParameter node){
        createError(node,"Generics are not supported in KeY");
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
        createError(node,"Annotations are not supported in KeY");
        return true;
    }

    @Override
    public boolean visit(EnumDeclaration node){
        createError(node,"Enums are not supported in KeY");
        return true;
    }

    @Override
    public boolean visit(SingleVariableDeclaration node){
        if(node.isVarargs())
            createError(node,"Varargs are not supported in KeY");
        return true;
    }

    @Override
    public boolean visit(EnumConstantDeclaration node){
        createError(node,"Enums are not supported in KeY");
        return true;
    }

    @Override
    public boolean visit(ImportDeclaration node){
        if(node.isStatic())
            createError(node,"Static imports are not supported in KeY");
        return true;
    }
    
    @Override
    public boolean visit(NumberLiteral node){
        if(node.getToken().indexOf('b')>=0)
            createError(node,"Binary literals are not supported in KeY");
        return true;
    }

    @Override
    public boolean visit(TryStatement node){
        if(node.resources().size()!=0)
            createError(node,"Try with resources is not supported in KeY");
        List<CatchClause> catchClauses = node.catchClauses();
        if(catchClauses.size() > 1){
            for(CatchClause catchClause: catchClauses)
                createError(catchClause,"Multiple catch clauses are not supported in KeY");
        }
        return true;
    }

    @Override
    public boolean visit(SimpleType node){
        String type = node.getName().getFullyQualifiedName();
        String message = "";
        switch(type){
            case "Runnable":
            case "Thread":
                message = "Multithreading is not supported in KeY";
                break;
        }
        if(message!="")
            createError(node,message);
        return true;
    }

    @Override
    public boolean visit(ArrayInitializer node){
        return visitExpression(node);
    }

    @Override
    public boolean visit(Assignment node){
        return visitExpression(node);
    }

    @Override
    public boolean visit(VariableDeclarationExpression node){
        return visitExpression(node);
    }

    public boolean visitExpression(Expression node){
        if(node.resolveBoxing() || node.resolveUnboxing())
            createError(node,"Autoboxing is not supported in KeY");
        return true;
        //TODO: Not working
    }

    @Override
    public boolean visit(MethodInvocation node){
        for(ITypeBinding implemented: node.resolveMethodBinding().getDeclaringClass().getInterfaces()){
            String qualifiedName = implemented.getQualifiedName();
            if(qualifiedName.equals("java.lang.Runnable") ||
                qualifiedName.equals("java.lang.Thread"))
                createError(node, "Multithreading is not supported in KeY");
        }
        return true;
    }

    /**
     * Creates and parses an AST from the source code
     * @return A list of Diagnostics, containing all features that are not supported by key with their respective positions in the source code
     */
    public List<Diagnostic> parseAst(CompilationUnit cu){
        // Apply the visitor on the created tree (visit methods above will be called on the nodes)
        cu.accept(this);
        return results;
    }
}
