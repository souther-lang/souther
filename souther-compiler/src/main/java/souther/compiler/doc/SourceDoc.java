package souther.compiler.doc;

import com.sun.source.tree.ArrayTypeTree;
import com.sun.source.tree.ClassTree;
import com.sun.source.tree.CompilationUnitTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.MemberSelectTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.ParameterizedTypeTree;
import com.sun.source.tree.PrimitiveTypeTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.TypeParameterTree;
import com.sun.source.tree.VariableTree;
import com.sun.source.util.DocTrees;
import com.sun.source.util.JavacTask;
import com.sun.source.util.TreePathScanner;

import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.SimpleJavaFileObject;
import javax.tools.ToolProvider;
import java.lang.constant.ClassDesc;
import java.lang.constant.MethodTypeDesc;
import java.net.URI;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * The documentation a Java source file carries, read with the compiler's own parser.
 *
 * <p>A member is identified by what it is — its enclosing type, its name, and the erased types of
 * its parameters — rather than by a key guessed from the text around it. That is the whole reason
 * for going through {@link JavacTask}: a reader that matches on names alone cannot tell a nested
 * type's method from its enclosing type's, or one overload from another, and attaches documentation
 * that is not true of the member it is printed against.
 *
 * <p>Where the parser is not there to be used — a runtime without {@code jdk.compiler} — nothing is
 * read. No documentation is the honest answer; someone else's is not.
 */
final class SourceDoc {

    static final SourceDoc NONE = new SourceDoc(Optional.empty(), Map.of());

    /** The documentation of the type asked for. */
    private final Optional<String> classDoc;

    /** {@code name(Erased,Types)} → its doc comment. The key names one member exactly. */
    private final Map<String, String> bySignature;

    private SourceDoc(Optional<String> classDoc, Map<String, String> bySignature) {
        this.classDoc = classDoc;
        this.bySignature = bySignature;
    }

    /**
     * Reads {@code source} for what it says about {@code binaryName}, which may name a type nested
     * inside the file's own top-level type.
     */
    static SourceDoc of(String source, String binaryName) {
        if (ToolProvider.getSystemJavaCompiler() == null) {
            return NONE;
        }
        try {
            return read(source, binaryName);
        } catch (RuntimeException | LinkageError | java.io.IOException e) {
            // A source that will not parse, or a runtime with no compiler in it, leaves the API
            // readable and undocumented, which is the failure this can afford.
            return NONE;
        }
    }

    Optional<String> classDoc() {
        return classDoc;
    }

    /** What the source says about a field of this name. */
    Optional<String> ofField(String name) {
        return Optional.ofNullable(bySignature.get(name));
    }

    /**
     * What the source says about the member with this name and these erased parameter types.
     *
     * <p>The types have to agree. Falling back to a name and a count when they do not is how the
     * documentation of one overload ends up over another — an overload that carries none of its own
     * leaves the count looking settled when it is not. A comment that cannot be matched is a
     * comment that goes unprinted.
     */
    Optional<String> ofMethod(String name, MethodTypeDesc type) {
        return Optional.ofNullable(bySignature.get(signature(name, type)));
    }

    /** The {@code @param} names of that member's doc comment, in the order they are written. */
    List<String> paramsOf(String name, MethodTypeDesc type) {
        return ofMethod(name, type).map(SourceDoc::paramNames).orElse(List.of());
    }

    private static List<String> paramNames(String doc) {
        List<String> params = new ArrayList<>();
        var m = java.util.regex.Pattern.compile("@param\\s+(?!<)(\\w+)").matcher(doc);
        while (m.find()) {
            params.add(m.group(1));
        }
        return params;
    }

    private static String signature(String name, MethodTypeDesc type) {
        List<String> params = new ArrayList<>();
        for (ClassDesc p : type.parameterList()) {
            params.add(erased(p));
        }
        return name + "(" + String.join(",", params) + ")";
    }

    /** A class file's parameter type, as the simple name the source would have written. */
    private static String erased(ClassDesc d) {
        if (d.isArray()) {
            return erased(d.componentType()) + "[]";
        }
        if (d.isPrimitive()) {
            return d.displayName();
        }
        String display = d.displayName();
        int nested = display.lastIndexOf('$');
        return nested < 0 ? display : display.substring(nested + 1);
    }

    // ---- reading ----

    private static SourceDoc read(String source, String binaryName) throws java.io.IOException {
        JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
        String simple = binaryName.substring(binaryName.lastIndexOf('.') + 1);
        String outermost = simple.split("\\$")[0];
        JavaFileObject file = new SimpleJavaFileObject(
                URI.create("string:///" + outermost + ".java"), JavaFileObject.Kind.SOURCE) {
            @Override
            public CharSequence getCharContent(boolean ignoreEncodingErrors) {
                return source;
            }
        };
        JavacTask task = (JavacTask) compiler.getTask(
                java.io.Writer.nullWriter(), null, diagnostic -> { }, List.of(), List.of(), List.of(file));
        DocTrees docs = DocTrees.instance(task);
        Iterable<? extends CompilationUnitTree> units = task.parse();

        Collector collector = new Collector(docs, simple);
        for (CompilationUnitTree unit : units) {
            collector.scan(unit, null);
        }
        return new SourceDoc(collector.classDoc, collector.bySignature);
    }

    /** Walks the file, keeping the chain of enclosing type names so a member is filed under the
     *  type it is actually declared in. */
    private static final class Collector extends TreePathScanner<Void, Void> {

        private final DocTrees docs;
        private final String target;
        private final Deque<String> enclosing = new ArrayDeque<>();

        /** Type-variable name → the erasure of its first bound, for every scope now open. */
        private final Deque<Map<String, String>> bounds = new ArrayDeque<>();

        private Optional<String> classDoc = Optional.empty();
        private final Map<String, String> bySignature = new LinkedHashMap<>();

        Collector(DocTrees docs, String target) {
            this.docs = docs;
            this.target = target;
        }

        private String here() {
            List<String> names = new ArrayList<>(enclosing);
            java.util.Collections.reverse(names);
            return String.join("$", names);
        }

        @Override
        public Void visitClass(ClassTree node, Void unused) {
            enclosing.push(node.getSimpleName().toString());
            bounds.push(boundsOf(node.getTypeParameters()));
            if (here().equals(target)) {
                classDoc = doc();
            }
            super.visitClass(node, unused);
            bounds.pop();
            enclosing.pop();
            return null;
        }

        @Override
        public Void visitMethod(MethodTree node, Void unused) {
            if (here().equals(target)) {
                bounds.push(boundsOf(node.getTypeParameters()));
                doc().ifPresent(text -> {
                    String name = node.getName().toString();
                    String shown = name.equals("<init>") ? target.substring(target.lastIndexOf('$') + 1) : name;
                    List<String> params = node.getParameters().stream()
                            .map(VariableTree::getType)
                            .map(this::erasedSource)
                            .toList();
                    bySignature.put(shown + "(" + String.join(",", params) + ")", text);
                });
                bounds.pop();
            }
            return super.visitMethod(node, unused);
        }

        private Map<String, String> boundsOf(List<? extends TypeParameterTree> parameters) {
            Map<String, String> scope = new HashMap<>();
            for (TypeParameterTree t : parameters) {
                scope.put(t.getName().toString(), t.getBounds().isEmpty() ? "Object" : null);
            }
            // Bounds are erased once the names they may refer to are all in scope.
            for (TypeParameterTree t : parameters) {
                if (scope.get(t.getName().toString()) == null) {
                    scope.put(t.getName().toString(), erasedSource(t.getBounds().getFirst()));
                }
            }
            return scope;
        }

        @Override
        public Void visitVariable(VariableTree node, Void unused) {
            Tree parent = getCurrentPath().getParentPath().getLeaf();
            if (parent instanceof ClassTree && here().equals(target)) {
                doc().ifPresent(text -> bySignature.put(node.getName().toString(), text));
            }
            return super.visitVariable(node, unused);
        }

        private Optional<String> doc() {
            String comment = docs.getDocComment(getCurrentPath());
            return comment == null || comment.isBlank() ? Optional.empty() : Optional.of(comment);
        }


        /** A written type as the class file will have erased it: no type arguments, a type
         *  variable as its bound, an array as its component with brackets. */
        private String erasedSource(Tree type) {
            return switch (type) {
                case ArrayTypeTree array -> erasedSource(array.getType()) + "[]";
                case ParameterizedTypeTree parameterized -> erasedSource(parameterized.getType());
                case PrimitiveTypeTree primitive -> primitive.getPrimitiveTypeKind().toString().toLowerCase();
                case MemberSelectTree member -> member.getIdentifier().toString();
                case IdentifierTree identifier -> {
                    String name = identifier.getName().toString();
                    for (Map<String, String> scope : bounds) {
                        String bound = scope.get(name);
                        if (bound != null) {
                            yield bound;
                        }
                    }
                    yield name;
                }
                default -> type.toString();
            };
        }
    }
}
