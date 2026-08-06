package souther.compiler.doc;

import com.sun.source.tree.ClassTree;
import com.sun.source.tree.CompilationUnitTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.VariableTree;
import com.sun.source.util.DocTrees;
import com.sun.source.util.JavacTask;
import com.sun.source.util.TreePathScanner;
import com.sun.source.util.Trees;

import javax.lang.model.element.Element;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.TypeElement;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.ArrayType;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;
import javax.lang.model.util.Elements;
import javax.lang.model.util.Types;
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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * The documentation a Java source file carries, read with the compiler's own front end.
 *
 * <p>A member is found by the name and the erased parameter types the class file will have given
 * it. Those are not guessed from how the source spelled them: the file is compiled against the same
 * class path the class was read from, and the types come back from {@link Types#erasure} as binary
 * names — the very strings the class file holds. A declaration whose types did not resolve is not
 * registered at all, so a member either matches what it was written as or goes undocumented.
 *
 * <p>This replaced a reader that matched on how names were spelled. Every rule that tried to make
 * spelling stand in for identity — the simple name, the parameter count, the set of qualifications
 * a file's imports allowed — had another case where two different members read the same, and each
 * one attached documentation to something it was not written for.
 *
 * <p>Where the front end is not there to be used — a runtime without {@code jdk.compiler} — nothing
 * is read. No documentation is the honest answer; someone else's is not.
 */
final class SourceDoc {

    static final SourceDoc NONE = new SourceDoc(Optional.empty(), Map.of(), Map.of(), Map.of());

    private final Optional<String> classDoc;
    private final Map<String, String> fields;
    private final Map<String, String> docs;
    private final Map<String, List<String>> parameterNames;

    private SourceDoc(Optional<String> classDoc, Map<String, String> fields,
                      Map<String, String> docs, Map<String, List<String>> parameterNames) {
        this.classDoc = classDoc;
        this.fields = fields;
        this.docs = docs;
        this.parameterNames = parameterNames;
    }

    /**
     * Reads {@code source} for what it says about {@code binaryName}, resolving the types it names
     * against {@code classPath} — the same path the class file itself was found on.
     */
    static SourceDoc of(String source, String binaryName, String classPath) {
        if (ToolProvider.getSystemJavaCompiler() == null) {
            return NONE;
        }
        try {
            return read(source, binaryName, classPath);
        } catch (RuntimeException | LinkageError | java.io.IOException e) {
            // A source that will not parse, or a runtime with no front end in it, leaves the API
            // readable and undocumented, which is the failure this can afford.
            return NONE;
        }
    }

    Optional<String> classDoc() {
        return classDoc;
    }

    /** What the source says about a field of this name. */
    Optional<String> ofField(String name) {
        return Optional.ofNullable(fields.get(name));
    }

    /** What the source says about the member the class file describes. */
    Optional<String> ofMethod(String name, MethodTypeDesc type) {
        return Optional.ofNullable(docs.get(key(name, type)));
    }

    /** The parameter names that member was declared with, in the order it declared them. A
     *  {@code @param} tag names a parameter rather than taking a position, so its order says
     *  nothing about theirs. */
    List<String> paramsOf(String name, MethodTypeDesc type) {
        return parameterNames.getOrDefault(key(name, type), List.of());
    }

    private static String key(String name, MethodTypeDesc type) {
        return name + "(" + String.join(",", type.parameterList().stream().map(SourceDoc::binary).toList()) + ")";
    }

    /** A class file's parameter type as its binary name. */
    private static String binary(ClassDesc d) {
        if (d.isArray()) {
            return binary(d.componentType()) + "[]";
        }
        if (d.isPrimitive()) {
            return d.displayName();
        }
        String pkg = d.packageName();
        return (pkg.isEmpty() ? "" : pkg + ".") + d.displayName();
    }

    // ---- reading ----

    private static SourceDoc read(String source, String binaryName, String classPath)
            throws java.io.IOException {
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
        List<String> options = classPath == null || classPath.isBlank()
                ? List.of() : List.of("-classpath", classPath);
        JavacTask task = (JavacTask) compiler.getTask(
                java.io.Writer.nullWriter(), null, diagnostic -> { }, options, List.of(), List.of(file));

        Iterable<? extends CompilationUnitTree> units = task.parse();
        // Types are wanted, not just trees: a name in a source file means whatever this file's
        // imports and this class path make it mean, and only the front end knows which.
        task.analyze();

        Collector collector = new Collector(DocTrees.instance(task), Trees.instance(task),
                task.getTypes(), task.getElements(), simple);
        for (CompilationUnitTree unit : units) {
            collector.scan(unit, null);
        }
        return new SourceDoc(collector.classDoc, collector.fields, collector.docs, collector.parameterNames);
    }

    /** Walks the file, keeping the chain of enclosing type names so a member is collected under the
     *  type it is actually declared in. */
    private static final class Collector extends TreePathScanner<Void, Void> {

        private final DocTrees docTrees;
        private final Trees trees;
        private final Types types;
        private final Elements elements;
        private final String target;
        private final Deque<String> enclosing = new ArrayDeque<>();

        private Optional<String> classDoc = Optional.empty();
        private final Map<String, String> fields = new LinkedHashMap<>();
        private final Map<String, String> docs = new LinkedHashMap<>();
        private final Map<String, List<String>> parameterNames = new LinkedHashMap<>();

        Collector(DocTrees docTrees, Trees trees, Types types, Elements elements, String target) {
            this.docTrees = docTrees;
            this.trees = trees;
            this.types = types;
            this.elements = elements;
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
            if (here().equals(target)) {
                classDoc = doc();
            }
            super.visitClass(node, unused);
            enclosing.pop();
            return null;
        }

        @Override
        public Void visitMethod(MethodTree node, Void unused) {
            if (here().equals(target)
                    && trees.getElement(getCurrentPath()) instanceof ExecutableElement member) {
                List<String> erased = erasedParameters(member);
                if (erased != null) {
                    String written = node.getName().toString();
                    // A constructor is named for its own type, not for the chain it is nested in.
                    String name = written.equals("<init>")
                            ? target.substring(target.lastIndexOf('$') + 1) : written;
                    String key = name + "(" + String.join(",", erased) + ")";
                    doc().ifPresent(text -> docs.put(key, text));
                    parameterNames.put(key, member.getParameters().stream()
                            .map(p -> p.getSimpleName().toString()).toList());
                }
            }
            return super.visitMethod(node, unused);
        }

        @Override
        public Void visitVariable(VariableTree node, Void unused) {
            Tree parent = getCurrentPath().getParentPath().getLeaf();
            if (parent instanceof ClassTree && here().equals(target)) {
                doc().ifPresent(text -> fields.put(node.getName().toString(), text));
            }
            return super.visitVariable(node, unused);
        }

        private Optional<String> doc() {
            String comment = docTrees.getDocComment(getCurrentPath());
            return comment == null || comment.isBlank() ? Optional.empty() : Optional.of(comment);
        }

        /** The binary names of this member's erased parameter types, or null where one of them did
         *  not resolve — a dependency of the library that is not on the class path it was read
         *  from. Unresolved is not matched against: it is the case a guess would fill in. */
        private List<String> erasedParameters(ExecutableElement member) {
            List<String> erased = new ArrayList<>();
            for (VariableElement parameter : member.getParameters()) {
                String name = binaryOf(types.erasure(parameter.asType()));
                if (name == null) {
                    return null;
                }
                erased.add(name);
            }
            return erased;
        }

        private String binaryOf(TypeMirror type) {
            if (type.getKind() == TypeKind.ARRAY) {
                String component = binaryOf(((ArrayType) type).getComponentType());
                return component == null ? null : component + "[]";
            }
            if (type.getKind().isPrimitive()) {
                return type.toString();
            }
            if (type.getKind() != TypeKind.DECLARED) {
                return null;
            }
            Element element = types.asElement(type);
            return element instanceof TypeElement declared
                    ? elements.getBinaryName(declared).toString() : null;
        }
    }
}
