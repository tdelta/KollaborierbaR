package linter;

import linter.Diagnostic;
import javax.tools.JavaFileObject;
import java.util.LinkedList;
import java.util.List;
import java.util.Arrays;
import com.sun.source.util.TreePathScanner;
import com.sun.source.util.Trees;
//import com.sun.source.tree.LambdaExpressionTree;
import com.sun.source.util.SourcePositions;
import com.sun.source.tree.CompilationUnitTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.TypeParameterTree;
import com.sun.source.tree.ParameterizedTypeTree;

import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;

public class JmlNotSupportedScanner extends TreePathScanner<List<Diagnostic>, Trees>{

    private List<JavaFileObject> sourceFile;
    private CompilationUnitTree compilationUnitTree;

    public void setCompilationUnitTree(CompilationUnitTree compilationUnitTree){
        this.compilationUnitTree = compilationUnitTree;
    }

    public JmlNotSupportedScanner(List<JavaFileObject> sourceFile){
        this.sourceFile = sourceFile;
    }

    /*@Override
    public List<Diagnostic> visitLambdaExpression(LambdaExpressionTree node,Trees trees){
        Diagnostic diagnostic = createError("Lambda expressions are not supported in key",node,trees);
        // The method from the superclass parses all children
        List<Diagnostic> result = super.visitLambdaExpression(node,trees);
        // If none of the visit methods for the children of this node was overridden in this class, the default null is returned
        if(result == null) result = new LinkedList<Diagnostic>();
        result.add(diagnostic);
        return result;
    }*/

    @Override
    public List<Diagnostic> visitLiteral(LiteralTree node, Trees trees){
        String message = null;
        if(node.getKind() == Tree.Kind.DOUBLE_LITERAL)
                message = "Doubles are not supported in key";
        if(node.getKind() == Tree.Kind.FLOAT_LITERAL)
                message = "Floats are not supported in key";

        if(message != null){
            LinkedList<Diagnostic> result = new LinkedList<Diagnostic>();
            result.add(createError(message,node,trees));
            return result;
        }
        return null;
    }

    @Override
    public List<Diagnostic> visitTypeParameter(TypeParameterTree node, Trees trees){
        Diagnostic diagnostic = createError("Generics are not supported in key",node,trees);
        // The method from the superclass parses all children
        List<Diagnostic> result = super.visitTypeParameter(node,trees);
        // If none of the visit methods for the children of this node was overridden in this class, the default null is returned
        if(result == null) result = new LinkedList<Diagnostic>();
        result.add(diagnostic);
        return result;
    }

    @Override
    public List<Diagnostic> visitParameterizedType(ParameterizedTypeTree node, Trees trees){
        Diagnostic diagnostic = createError("Generics are not supported in key",node,trees);
        // The method from the superclass parses all children
        List<Diagnostic> result = new LinkedList<Diagnostic>();
        // If none of the visit methods for the children of this node was overridden in this class, the default null is returned
        // if(result == null) result = new LinkedList<Diagnostic>();
        result.add(diagnostic);
        return result;
    }

    private Diagnostic createError(String message, Tree node,Trees trees){
        SourcePositions positions = trees.getSourcePositions();
        Diagnostic diagnostic = new Diagnostic(
            message, // error message 
            positions.getStartPosition(compilationUnitTree,node), // gets the absolute start position of the ast node in the source code
            positions.getEndPosition(compilationUnitTree,node), // gets the absolute end position of the ast node in the source code
            sourceFile.get(0), // Source file
            Diagnostic.Kind.ERROR); // Type of diagnostic 
        return diagnostic;
    }

    @Override
    public List<Diagnostic> reduce(List<Diagnostic> d1, List<Diagnostic> d2){
        // If one list is null return the other. If both are null return null
        if(d1 == null){
            if(d2 == null){
                return null;
            }
            return d2;
        }
        if(d2 == null) return d1;
        // merge the linked lists
        d1.addAll(d2);
        return d1;
    }
}
