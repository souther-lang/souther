package souther.compiler.doc;

import com.sun.source.tree.ArrayTypeTree;
import com.sun.source.tree.ClassTree;
import com.sun.source.tree.CompilationUnitTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.ImportTree;
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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The documentation a Java source file carries, read with the compiler's own parser.
 *
 * <p>A member is matched to a declaration, not to a key spelled from its name. The parser gives the
 * enclosing type as a scope and the parameters as they were written; a class file gives the erased
 * types they became. A declaration answers for a member when every parameter it declares could have
 * erased to the one the class file has, and when no other declaration could have. Where two might,
 * neither is used: this is the only thing between a reader and documentation written for something
 * else, which three rounds of narrower keys did not manage to be.
 *
 * <p>Where the parser is not there to be used — a runtime without {@code jdk.compiler} — nothing is
 * read. No documentation is the honest answer; someone else's is not.
 */
final class SourceDoc {

    static final SourceDoc NONE = new SourceDoc(Optional.empty(), Map.of(), List.of());

    /** What a source file says about one method or constructor of the type asked for. */
    private record Declared(String name, List<Set<String>> parameters, List<String> parameterNames,
                            Optional<String> doc) {

        /** Whether this declaration could be the member the class file describes. */
        boolean couldBe(String memberName, List<String> erased) {
            if (!name.equals(memberName) || parameters.size() != erased.size()) {
                return false;
            }
            for (int i = 0; i < erased.size(); i++) {
                if (!parameters.get(i).contains(erased.get(i))) {
                    return false;
                }
            }
            return true;
        }
    }

    private final Optional<String> classDoc;
    private final Map<String, String> fields;
    private final List<Declared> members;

    private SourceDoc(Optional<String> classDoc, Map<String, String> fields, List<Declared> members) {
        this.classDoc = classDoc;
        this.fields = fields;
        this.members = members;
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
        return Optional.ofNullable(fields.get(name));
    }

    /** What the source says about the member the class file describes, where one declaration and
     *  only one could be it. */
    Optional<String> ofMethod(String name, MethodTypeDesc type) {
        return only(name, type).flatMap(Declared::doc);
    }

    /** The parameter names that member was declared with — the declaration's own, in its own order.
     *  A {@code @param} tag names a parameter rather than taking a position, so its order says
     *  nothing about theirs. */
    List<String> paramsOf(String name, MethodTypeDesc type) {
        return only(name, type).map(Declared::parameterNames).orElse(List.of());
    }

    private Optional<Declared> only(String name, MethodTypeDesc type) {
        List<String> erased = type.parameterList().stream().map(SourceDoc::erased).toList();
        List<Declared> could = members.stream().filter(d -> d.couldBe(name, erased)).toList();
        return could.size() == 1 ? Optional.of(could.getFirst()) : Optional.empty();
    }

    /** A class file's parameter type, fully qualified, with a nested type spelled as its source
     *  would spell it so the two can be compared. */
    private static String erased(ClassDesc d) {
        if (d.isArray()) {
            return erased(d.componentType()) + "[]";
        }
        if (d.isPrimitive()) {
            return d.displayName();
        }
        String pkg = d.packageName();
        return (pkg.isEmpty() ? "" : pkg + ".") + d.displayName().replace('$', '.');
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

        Collector collector = new Collector(docs, simple);
        for (CompilationUnitTree unit : task.parse()) {
            collector.scan(unit, null);
        }
        return new SourceDoc(collector.classDoc, collector.fields, collector.members);
    }

    /** Walks the file, keeping the chain of enclosing type names so a member is collected under the
     *  type it is actually declared in. */
    private static final class Collector extends TreePathScanner<Void, Void> {

        private final DocTrees docs;
        private final String target;
        private final Deque<String> enclosing = new ArrayDeque<>();

        /** Type-variable name → the erasure of its first bound, for every scope now open. */
        private final Deque<Map<String, String>> bounds = new ArrayDeque<>();

        /** Simple name → what it may stand for here: an explicit import, this file's own package,
         *  a package imported wholesale, or {@code java.lang}. */
        private final Map<String, Set<String>> imported = new HashMap<>();
        private final List<String> onDemand = new ArrayList<>();
        private String packageName = "";

        private Optional<String> classDoc = Optional.empty();
        private final Map<String, String> fields = new LinkedHashMap<>();
        private final List<Declared> members = new ArrayList<>();

        Collector(DocTrees docs, String target) {
            this.docs = docs;
            this.target = target;
        }

        @Override
        public Void visitCompilationUnit(CompilationUnitTree node, Void unused) {
            packageName = node.getPackageName() == null ? "" : node.getPackageName().toString();
            for (ImportTree i : node.getImports()) {
                if (i.isStatic()) {
                    continue;
                }
                String written = i.getQualifiedIdentifier().toString();
                if (written.endsWith(".*")) {
                    onDemand.add(written.substring(0, written.length() - 2));
                } else {
                    imported.computeIfAbsent(written.substring(written.lastIndexOf('.') + 1),
                            k -> new LinkedHashSet<>()).add(written);
                }
            }
            return super.visitCompilationUnit(node, unused);
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
                String written = node.getName().toString();
                // A constructor is named for its own type, not for the chain it is nested in.
                String name = written.equals("<init>")
                        ? target.substring(target.lastIndexOf('$') + 1) : written;
                members.add(new Declared(name,
                        node.getParameters().stream().map(p -> candidates(p.getType())).toList(),
                        node.getParameters().stream().map(p -> p.getName().toString()).toList(),
                        doc()));
                bounds.pop();
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
            String comment = docs.getDocComment(getCurrentPath());
            return comment == null || comment.isBlank() ? Optional.empty() : Optional.of(comment);
        }

        private Map<String, String> boundsOf(List<? extends TypeParameterTree> parameters) {
            Map<String, String> scope = new HashMap<>();
            parameters.forEach(t -> scope.put(t.getName().toString(), "java.lang.Object"));
            for (TypeParameterTree t : parameters) {
                if (!t.getBounds().isEmpty()) {
                    Set<String> bound = candidates(t.getBounds().getFirst());
                    if (bound.size() == 1) {
                        scope.put(t.getName().toString(), bound.iterator().next());
                    }
                }
            }
            return scope;
        }

        /**
         * Every fully-qualified type the written type could be, erased.
         *
         * <p>A source file names a type the way its imports let it, and a class file names it in
         * full. Rather than resolve the one into the other — which needs the library's own class
         * path, and this has none — every reading the file allows is kept, and a declaration
         * answers for a member only when no sibling declaration allows the same reading.
         */
        private Set<String> candidates(Tree type) {
            return switch (type) {
                case ArrayTypeTree array -> candidates(array.getType()).stream()
                        .map(c -> c + "[]").collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new));
                case ParameterizedTypeTree parameterized -> candidates(parameterized.getType());
                case PrimitiveTypeTree primitive ->
                        Set.of(primitive.getPrimitiveTypeKind().toString().toLowerCase());
                case MemberSelectTree member -> qualified(member.toString());
                case IdentifierTree identifier -> named(identifier.getName().toString());
                default -> Set.of(type.toString());
            };
        }

        /** A name written with dots may already be complete, or may be a nested type reached
         *  through a simple name this file can resolve. */
        private Set<String> qualified(String written) {
            Set<String> all = new LinkedHashSet<>();
            all.add(written);
            int firstDot = written.indexOf('.');
            String head = written.substring(0, firstDot);
            String tail = written.substring(firstDot);
            named(head).forEach(c -> all.add(c + tail));
            return all;
        }

        private Set<String> named(String simple) {
            for (Map<String, String> scope : bounds) {
                String bound = scope.get(simple);
                if (bound != null) {
                    return Set.of(bound);
                }
            }
            Set<String> all = new LinkedHashSet<>();
            if (imported.containsKey(simple)) {
                all.addAll(imported.get(simple));
                return all;   // an explicit import settles it
            }
            List<String> chain = new ArrayList<>(enclosing);
            java.util.Collections.reverse(chain);
            for (int i = chain.size(); i > 0; i--) {
                all.add(prefixed(String.join(".", chain.subList(0, i)) + "." + simple));
            }
            all.add(prefixed(simple));
            onDemand.forEach(p -> all.add(p + "." + simple));
            if (isJavaLang(simple)) {
                all.add("java.lang." + simple);
            }
            return all;
        }

        private String prefixed(String name) {
            return packageName.isEmpty() ? name : packageName + "." + name;
        }

        private static boolean isJavaLang(String simple) {
            try {
                Class.forName("java.lang." + simple);
                return true;
            } catch (ClassNotFoundException | LinkageError e) {
                return false;
            }
        }
    }
}
