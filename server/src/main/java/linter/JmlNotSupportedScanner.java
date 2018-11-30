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

    private void createError(ASTNode node,String message){
        int startPos = node.getStartPosition();
        int endPos = startPos + node.getLength();
        results.add(new Diagnostic(
            message,
            startPos,
            endPos,
            sourceFile,
            Diagnostic.Kind.ERROR));
    }

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
        // TODO: Not working
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
        // TODO: Not working
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

    // TODO: Imported classes that implement runnable or Thread
    // TODO: Does KeY support Autoboxing?

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
