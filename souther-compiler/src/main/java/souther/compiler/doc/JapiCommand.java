package souther.compiler.doc;

import java.io.IOException;
import java.io.PrintStream;
import java.io.UncheckedIOException;
import java.lang.classfile.Attributes;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.ClassSignature;
import java.lang.classfile.FieldModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.MethodSignature;
import java.lang.classfile.Signature;
import java.lang.classfile.attribute.MethodParameterInfo;
import java.lang.constant.ClassDesc;
import java.lang.constant.MethodTypeDesc;
import java.lang.reflect.AccessFlag;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.zip.ZipEntry;

/**
 * {@code souther japi}: a dependency's public API, read straight from its class files — the
 * question javap is reached for — with the javadoc brought along from the {@code -sources.jar}
 * sitting next to the jar, which javap never shows.
 *
 * <p>Nothing is class-loaded: the bytes are parsed, so no static initializer of the dependency
 * runs for the sake of printing its surface.
 */
public final class JapiCommand {

    private JapiCommand() {}

    public static int run(String[] args, PrintStream out, PrintStream err) {
        return run(args, out, err, JapiCommand.class.getClassLoader());
    }

    static int run(String[] args, PrintStream out, PrintStream err, ClassLoader bundled) {
        String name = null;
        List<Path> entries = new ArrayList<>();
        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case "-cp", "--class-path" -> {
                    if (i + 1 == args.length) {
                        err.println("-cp needs a path");
                        return 2;
                    }
                    for (String p : args[++i].split(java.io.File.pathSeparator)) {
                        entries.add(Path.of(p));
                    }
                }
                default -> name = args[i];
            }
        }
        if (name == null) {
            err.println("usage: souther japi <class-or-package> [-cp <path>]");
            return 2;
        }
        if (entries.isEmpty()) {
            for (String p : System.getProperty("java.class.path", "").split(java.io.File.pathSeparator)) {
                if (!p.isEmpty()) {
                    entries.add(Path.of(p));
                }
            }
        }

        String member = null;
        int hash = name.indexOf('#');
        if (hash >= 0) {
            member = name.substring(hash + 1);
            name = name.substring(0, hash);
        }

        Found found = findClass(name, entries, err);
        if (found != null) {
            return print(found, name, member, out, err, bundled);
        }
        if (member != null) {
            err.println("no class `" + name + "` on the class path:");
            entries.forEach(e -> err.println("  " + e));
            return 2;
        }
        List<String> classes = classesUnder(name, entries, err);
        if (!classes.isEmpty()) {
            classes.forEach(out::println);
            return 0;
        }
        err.println("no class or package `" + name + "` on the class path:");
        entries.forEach(e -> err.println("  " + e));
        return 2;
    }

    /** A class's bytes and the classpath entry they came from — kept together because the
     *  sources jar, and with it the javadoc, is found from the entry. */
    private record Found(byte[] bytes, Path entry) {}

    private static Found findClass(String binaryName, List<Path> entries, PrintStream err) {
        String resource = binaryName.replace('.', '/') + ".class";
        for (Path entry : entries) {
            try {
                if (Files.isDirectory(entry)) {
                    Path f = entry.resolve(resource);
                    if (Files.isRegularFile(f)) {
                        return new Found(Files.readAllBytes(f), entry);
                    }
                } else if (Files.isRegularFile(entry)) {
                    try (JarFile jar = versioned(entry)) {
                        ZipEntry e = jar.getEntry(resource);
                        if (e != null) {
                            return new Found(jar.getInputStream(e).readAllBytes(), entry);
                        }
                    }
                }
            } catch (IOException e) {
                unreadable(entry, e, err);
            }
        }
        return null;
    }

    /** A class path is given, not chosen: one entry that cannot be opened is said and stepped
     *  over, so the entries beside it still answer. */
    private static void unreadable(Path entry, IOException e, PrintStream err) {
        err.println("skipping `" + entry + "`: " + e.getMessage());
    }

    /**
     * The published top-level types of {@code packageName}.
     *
     * <p>A class file's name says nothing about whether anyone outside its package may name the
     * type. This command answers a dependency's public API, so the class's own access flag decides,
     * and {@code package-info} — a descriptor rather than a type — is left out with it.
     */
    private static List<String> classesUnder(String packageName, List<Path> entries, PrintStream err) {
        String prefix = packageName.replace('.', '/') + "/";
        List<String> classes = new ArrayList<>();
        for (Path entry : entries) {
            try {
                if (Files.isDirectory(entry)) {
                    Path dir = entry.resolve(packageName.replace('.', '/'));
                    if (Files.isDirectory(dir)) {
                        try (var files = Files.list(dir)) {
                            for (Path f : files.toList()) {
                                String simple = topLevelName(f.getFileName().toString());
                                if (simple != null && isPublic(Files.readAllBytes(f))) {
                                    classes.add(packageName + "." + simple);
                                }
                            }
                        }
                    }
                } else if (Files.isRegularFile(entry)) {
                    try (JarFile jar = versioned(entry)) {
                        for (JarEntry e : jar.versionedStream().toList()) {
                            String name = e.getName();
                            if (!name.startsWith(prefix)) {
                                continue;
                            }
                            String simple = topLevelName(name.substring(prefix.length()));
                            if (simple == null || simple.contains("/")) {
                                continue;
                            }
                            try (java.io.InputStream in = jar.getInputStream(e)) {
                                if (isPublic(in.readAllBytes())) {
                                    classes.add(packageName + "." + simple);
                                }
                            }
                        }
                    }
                }
            } catch (IOException e) {
                unreadable(entry, e, err);
            }
        }
        return classes.stream().distinct().sorted().toList();
    }

    /** The simple name of a top-level class file, or null for a nested type or a descriptor. */
    private static String topLevelName(String fileName) {
        if (!fileName.endsWith(".class") || fileName.contains("$")) {
            return null;
        }
        String simple = fileName.substring(0, fileName.length() - ".class".length());
        return simple.equals("package-info") || simple.equals("module-info") ? null : simple;
    }

    private static boolean isPublic(byte[] bytes) {
        return ClassFile.of().parse(bytes).flags().flags().contains(AccessFlag.PUBLIC);
    }

    /**
     * A jar read at the version this JVM runs at.
     *
     * <p>A multi-release jar holds a class more than once, and the plain constructor answers with
     * the base copy — which is not what the caller's code links against. The shipped CLI jar is
     * itself multi-release, so this is the ordinary case rather than an exotic one.
     */
    private static JarFile versioned(Path entry) throws IOException {
        return new JarFile(entry.toFile(), true, java.util.zip.ZipFile.OPEN_READ, JarFile.runtimeVersion());
    }

    // ---- rendering ----

    private static int print(Found found, String binaryName, String member, PrintStream out,
                             PrintStream err, ClassLoader bundled) {
        ClassModel cm = ClassFile.of().parse(found.bytes());
        String simpleName = binaryName.substring(binaryName.lastIndexOf('.') + 1);
        // How many members share a name and a parameter count decides whether a doc comment filed
        // under that pair can belong to one of them. It is counted from the class file, because an
        // overload that carries no documentation of its own is invisible in the source reader and
        // would otherwise take its namesake's.
        java.util.Map<String, Integer> overloads = new java.util.HashMap<>();
        for (MethodModel m : cm.methods()) {
            Set<AccessFlag> flags = m.flags().flags();
            String methodName = m.methodName().stringValue();
            // A bridge is the compiler's, not the author's: counting it would make a method the
            // only one of its name in the source look like one of two, and lose its documentation.
            if (flags.contains(AccessFlag.BRIDGE) || flags.contains(AccessFlag.SYNTHETIC)
                    || methodName.equals("<clinit>")) {
                continue;
            }
            String shown = methodName.equals("<init>") ? simpleName : methodName;
            overloads.merge(shown + "/" + m.methodTypeSymbol().parameterCount(), 1, Integer::sum);
        }
        SourceDoc doc = SourceDoc.of(found.entry(), binaryName, overloads);
        if (!cm.flags().flags().contains(AccessFlag.PUBLIC)) {
            // Asked for by name, so it is answered — but a caller outside its package cannot name
            // it, and this command's subject is what a dependency publishes.
            err.println("`" + binaryName + "` is not public, so it is not part of what this jar publishes");
        }

        List<String> members = new ArrayList<>();
        StringBuilder body = new StringBuilder();
        for (FieldModel f : cm.fields()) {
            if (!visible(f.flags().flags())) {
                continue;
            }
            String name = f.fieldName().stringValue();
            members.add(name);
            if (member != null && !member.equals(name)) {
                continue;
            }
            body.append("\n");
            doc.of(name, -1).ifPresent(d -> body.append(indent(d)).append("\n"));
            body.append("  ").append(fieldLine(f)).append("\n");
        }
        for (MethodModel m : cm.methods()) {
            Set<AccessFlag> flags = m.flags().flags();
            if (!visible(flags) || flags.contains(AccessFlag.BRIDGE) || flags.contains(AccessFlag.SYNTHETIC)) {
                continue;
            }
            String methodName = m.methodName().stringValue();
            if (methodName.equals("<clinit>")) {
                continue;
            }
            String shown = methodName.equals("<init>") ? simpleName : methodName;
            members.add(shown);
            if (member != null && !member.equals(shown)) {
                continue;
            }
            body.append("\n");
            int arity = m.methodTypeSymbol().parameterCount();
            doc.of(shown, arity).ifPresent(d -> body.append(indent(d)).append("\n"));
            body.append("  ").append(methodLine(m, simpleName, doc)).append("\n");
        }
        if (member != null && body.isEmpty()) {
            err.println("`" + binaryName + "` has no public member `" + member + "`");
            err.println("members: " + String.join(", ", members.stream().distinct().toList()));
            return 2;
        }
        if (member == null) {
            doc.classDoc().ifPresent(out::println);
        }
        out.println(classHeader(cm, binaryName) + " {");
        out.print(body);
        out.println("}");
        return 0;
    }

    private static boolean visible(Set<AccessFlag> flags) {
        return flags.contains(AccessFlag.PUBLIC) || flags.contains(AccessFlag.PROTECTED);
    }

    private static String classHeader(ClassModel cm, String binaryName) {
        Set<AccessFlag> flags = cm.flags().flags();
        StringBuilder sb = new StringBuilder();
        if (flags.contains(AccessFlag.PUBLIC)) {
            sb.append("public ");
        }
        boolean iface = flags.contains(AccessFlag.INTERFACE);
        boolean enums = flags.contains(AccessFlag.ENUM);
        boolean record = cm.findAttribute(Attributes.record()).isPresent();
        if (flags.contains(AccessFlag.FINAL) && !enums && !record) {
            sb.append("final ");
        }
        if (flags.contains(AccessFlag.ABSTRACT) && !iface) {
            sb.append("abstract ");
        }
        sb.append(iface ? "interface " : enums ? "enum " : record ? "record " : "class ");
        sb.append(binaryName);

        Optional<ClassSignature> sig = cm.findAttribute(Attributes.signature())
                .map(a -> ClassSignature.parseFrom(a.signature().stringValue()));
        sig.ifPresent(s -> sb.append(typeParams(s.typeParameters())));

        String superName = cm.superclass().map(s -> s.asInternalName().replace('/', '.')).orElse("");
        String superShown = sig.map(s -> show(s.superclassSignature()))
                .orElse(shortName(superName));
        if (!iface && !superShown.equals("Object") && !superShown.equals("Record")
                && !superShown.equals("Enum") && !superShown.startsWith("Enum<")) {
            sb.append(" extends ").append(superShown);
        }
        List<String> interfaces = sig
                .map(s -> s.superinterfaceSignatures().stream().map(JapiCommand::show).toList())
                .orElseGet(() -> cm.interfaces().stream()
                        .map(i -> shortName(i.asInternalName().replace('/', '.'))).toList());
        if (!interfaces.isEmpty()) {
            sb.append(iface ? " extends " : " implements ").append(String.join(", ", interfaces));
        }
        return sb.toString();
    }

    private static String fieldLine(FieldModel f) {
        String type = f.findAttribute(Attributes.signature())
                .map(a -> show(Signature.parseFrom(a.signature().stringValue())))
                .orElse(shortName(desc(f.fieldTypeSymbol())));
        return memberFlags(f.flags().flags()) + type + " " + f.fieldName().stringValue();
    }

    private static String methodLine(MethodModel m, String simpleName, SourceDoc doc) {
        Set<AccessFlag> flags = m.flags().flags();
        boolean ctor = m.methodName().stringValue().equals("<init>");
        StringBuilder sb = new StringBuilder(memberFlags(flags));
        Optional<MethodSignature> sig = m.findAttribute(Attributes.signature())
                .map(a -> MethodSignature.parseFrom(a.signature().stringValue()));
        sig.ifPresent(s -> sb.append(typeParams(s.typeParameters())).append(s.typeParameters().isEmpty() ? "" : " "));

        MethodTypeDesc mt = m.methodTypeSymbol();
        List<String> paramTypes = sig
                .map(s -> s.arguments().stream().map(JapiCommand::show).toList())
                .orElseGet(() -> mt.parameterList().stream().map(p -> shortName(desc(p))).toList());
        if (!ctor) {
            sb.append(sig.map(s -> show(s.result())).orElse(shortName(desc(mt.returnType())))).append(" ");
        }
        sb.append(ctor ? simpleName : m.methodName().stringValue()).append("(");
        String shown = ctor ? simpleName : m.methodName().stringValue();
        List<String> names = paramNames(m, paramTypes.size(),
                doc.paramsOf(shown, mt.parameterCount()));
        for (int i = 0; i < paramTypes.size(); i++) {
            if (i > 0) {
                sb.append(", ");
            }
            sb.append(paramTypes.get(i)).append(" ").append(names.get(i));
        }
        sb.append(")");
        // A checked exception is not a remark about the method, it is part of how it is called: a
        // caller who neither catches nor declares it does not compile.
        List<String> thrown = sig.map(s -> s.throwableSignatures().stream().map(JapiCommand::show).toList())
                .filter(t -> !t.isEmpty())
                .orElseGet(() -> m.findAttribute(Attributes.exceptions())
                        .map(a -> a.exceptions().stream()
                                .map(e -> shortName(e.asInternalName().replace('/', '.')))
                                .toList())
                        .orElse(List.of()));
        if (!thrown.isEmpty()) {
            sb.append(" throws ").append(String.join(", ", thrown));
        }
        return sb.toString();
    }

    private static List<String> paramNames(MethodModel m, int count, List<String> fromDoc) {
        List<MethodParameterInfo> given = m.findAttribute(Attributes.methodParameters())
                .map(a -> a.parameters()).orElse(List.of());
        List<String> names = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            // A generic method's signature omits synthetic leading parameters, so when the
            // MethodParameters list is longer than the signature, the tail names are the real ones.
            int fromEnd = given.size() - count + i;
            String name = fromEnd >= 0 && fromEnd < given.size()
                    ? given.get(fromEnd).name().map(n -> n.stringValue()).orElse(null)
                    : null;
            // Most libraries are not compiled with -parameters, and `arg0, arg1, arg2` says nothing
            // about which String is the code and which the message. The javadoc `@param` order is
            // the declaration order, so it names them where the class file does not.
            if (name == null && i < fromDoc.size()) {
                name = fromDoc.get(i);
            }
            names.add(name == null ? "arg" + i : name);
        }
        return names;
    }

    private static String memberFlags(Set<AccessFlag> flags) {
        StringBuilder sb = new StringBuilder();
        if (flags.contains(AccessFlag.PUBLIC)) {
            sb.append("public ");
        }
        if (flags.contains(AccessFlag.PROTECTED)) {
            sb.append("protected ");
        }
        if (flags.contains(AccessFlag.STATIC)) {
            sb.append("static ");
        }
        if (flags.contains(AccessFlag.FINAL)) {
            sb.append("final ");
        }
        if (flags.contains(AccessFlag.ABSTRACT)) {
            sb.append("abstract ");
        }
        return sb.toString();
    }

    private static String typeParams(List<Signature.TypeParam> params) {
        if (params.isEmpty()) {
            return "";
        }
        List<String> shown = new ArrayList<>();
        for (Signature.TypeParam p : params) {
            List<String> bounds = new ArrayList<>();
            p.classBound().filter(b -> !show(b).equals("Object")).map(JapiCommand::show).ifPresent(bounds::add);
            p.interfaceBounds().forEach(b -> bounds.add(show(b)));
            shown.add(p.identifier() + (bounds.isEmpty() ? "" : " extends " + String.join(" & ", bounds)));
        }
        return "<" + String.join(", ", shown) + ">";
    }

    private static String show(Signature sig) {
        return switch (sig) {
            case Signature.BaseTypeSig base -> switch (base.baseType()) {
                case 'B' -> "byte";
                case 'C' -> "char";
                case 'D' -> "double";
                case 'F' -> "float";
                case 'I' -> "int";
                case 'J' -> "long";
                case 'S' -> "short";
                case 'Z' -> "boolean";
                case 'V' -> "void";
                default -> String.valueOf(base.baseType());
            };
            case Signature.TypeVarSig var -> var.identifier();
            case Signature.ArrayTypeSig array -> show(array.componentSignature()) + "[]";
            case Signature.ClassTypeSig cls -> {
                StringBuilder sb = new StringBuilder(shortName(cls.className().replace('/', '.')));
                if (!cls.typeArgs().isEmpty()) {
                    sb.append("<").append(String.join(", ",
                            cls.typeArgs().stream().map(JapiCommand::show).toList())).append(">");
                }
                yield sb.toString();
            }
        };
    }

    private static String show(Signature.TypeArg arg) {
        return switch (arg) {
            case Signature.TypeArg.Unbounded _ -> "?";
            case Signature.TypeArg.Bounded b -> switch (b.wildcardIndicator()) {
                case NONE -> show(b.boundType());
                case EXTENDS -> "? extends " + show(b.boundType());
                case SUPER -> "? super " + show(b.boundType());
            };
        };
    }

    private static String desc(ClassDesc d) {
        if (d.isArray()) {
            return desc(d.componentType()) + "[]";
        }
        if (d.isPrimitive()) {
            return d.displayName();
        }
        String pkg = d.packageName();
        return pkg.isEmpty() ? d.displayName() : pkg + "." + d.displayName();
    }

    /** {@code java.lang} needs no spelling out; everything else keeps its package. */
    private static String shortName(String dotted) {
        return dotted.startsWith("java.lang.") && dotted.indexOf('.', "java.lang.".length()) < 0
                ? dotted.substring("java.lang.".length())
                : dotted;
    }

    private static String indent(String docBlock) {
        return docBlock.lines().map(l -> "  " + l.strip()).reduce((a, b) -> a + "\n" + b).orElse("");
    }

    // ---- javadoc from the sources jar ----

    /** The doc comments of one top-level source file, keyed by the name they precede. */
    private record SourceDoc(Optional<String> classDoc, java.util.Map<String, String> byName) {

        private static final SourceDoc NONE = new SourceDoc(Optional.empty(), java.util.Map.of());

        /**
         * The javadoc for {@code binaryName}, taken only from the artifact the class itself was
         * read from: the {@code -sources.jar} beside it, or sources carried inside it.
         *
         * <p>Sources carried inside are what the ordinary invocation needs, since the CLI is one
         * shaded jar with its dependencies inside it and nothing beside it. They are read out of
         * that same jar rather than off this tool's class path, because the two are not the same
         * question — a class taken from some other copy of a library must not be described by the
         * copy this tool happens to carry. Where the versions differ, the prose is wrong and the
         * parameter names taken from {@code @param} are wrong with it.
         */
        static SourceDoc of(Path entry, String binaryName, java.util.Map<String, Integer> overloads) {
            // A nested type is declared inside another type's file, and this reader has no notion
            // of where one declaration ends and the next begins: everything it finds would be
            // attributed to whichever type was asked for. Saying nothing is the only answer it can
            // make true for these.
            if (binaryName.contains("$")) {
                return NONE;
            }
            String outermost = binaryName;
            String simpleName = outermost.substring(outermost.lastIndexOf('.') + 1);
            String path = outermost.replace('.', '/') + ".java";

            String source = besideJar(entry, path);
            if (source == null) {
                source = carriedInside(entry, "META-INF/souther-sources/" + path);
            }
            return source == null ? NONE : parse(source, simpleName, overloads);
        }

        /** A source carried inside {@code entry} itself, at {@code path}. */
        private static String carriedInside(Path entry, String path) {
            if (!Files.isRegularFile(entry) || !entry.getFileName().toString().endsWith(".jar")) {
                return null;
            }
            try (JarFile jar = versioned(entry)) {
                ZipEntry e = jar.getEntry(path);
                return e == null ? null
                        : new String(jar.getInputStream(e).readAllBytes(), StandardCharsets.UTF_8);
            } catch (IOException ex) {
                throw new UncheckedIOException(ex);
            }
        }

        private static String besideJar(Path entry, String path) {
            String file = entry.getFileName().toString();
            if (!file.endsWith(".jar")) {
                return null;
            }
            Path sources = entry.resolveSibling(file.substring(0, file.length() - 4) + "-sources.jar");
            if (!Files.isRegularFile(sources)) {
                return null;
            }
            try (JarFile jar = new JarFile(sources.toFile())) {
                ZipEntry e = jar.getEntry(path);
                return e == null ? null
                        : new String(jar.getInputStream(e).readAllBytes(), StandardCharsets.UTF_8);
            } catch (IOException ex) {
                throw new UncheckedIOException(ex);
            }
        }


        /** What a doc comment is filed under when two of them would otherwise collide. */
        private static final String AMBIGUOUS = " ambiguous";

        static SourceDoc parse(String source, String simpleName, java.util.Map<String, Integer> overloads) {
            java.util.Map<String, String> byName = new java.util.LinkedHashMap<>();
            Optional<String> classDoc = Optional.empty();
            // Annotations may sit between the doc comment and the declaration it documents; they
            // are skipped, or the doc would be keyed by the annotation's own name-with-parentheses.
            var m = java.util.regex.Pattern
                    .compile("(/\\*\\*.*?\\*/)\\s*\\n(?:\\s*@[^\\n]*\\n)*\\s*([^\\n]*)",
                            java.util.regex.Pattern.DOTALL)
                    .matcher(source);
            while (m.find()) {
                String doc = m.group(1);
                String declaration = m.group(2);
                // A field's initializer may call a constructor — `Issues EMPTY = new Issues(...)` —
                // so a declaration whose `=` comes before any `(` is the field, not that call.
                int assign = declaration.indexOf('=');
                int paren = declaration.indexOf('(');
                var named = java.util.regex.Pattern
                        .compile("(?:class|interface|record|enum)\\s+(\\w+)|(\\w+)\\s*\\(")
                        .matcher(declaration);
                if (!named.find() || (assign >= 0 && (paren < 0 || assign < paren))) {
                    var field = java.util.regex.Pattern.compile("(\\w+)\\s*[=;]").matcher(declaration);
                    if (field.find()) {
                        byName.putIfAbsent(field.group(1), doc);
                    }
                    continue;
                }
                String typeName = named.group(1);
                if (typeName != null) {
                    if (typeName.equals(simpleName) && classDoc.isEmpty()) {
                        classDoc = Optional.of(doc);
                    } else {
                        byName.putIfAbsent(typeName, doc);
                    }
                } else {
                    // A method is filed under its name and how many parameters it takes, so an
                    // overload of a different length does not answer for this one. Two overloads
                    // of the same length are told apart by their parameter types, which this reader
                    // does not resolve — so neither is filed, and the members print with no prose
                    // rather than with another method's.
                    String key = named.group(2) + "/" + arityAt(source, m.start(2) + named.end(2));
                    if (overloads.getOrDefault(key, 1) > 1) {
                        // More than one member answers to this name and count, and telling them
                        // apart needs the parameter types this reader does not resolve. One of them
                        // may well be undocumented, which is exactly when a comment filed here
                        // would be printed against the wrong member.
                        byName.put(key, AMBIGUOUS);
                        continue;
                    }
                    String had = byName.putIfAbsent(key, doc);
                    if (had != null && !had.equals(doc)) {
                        byName.put(key, AMBIGUOUS);
                    }
                }
            }
            return new SourceDoc(classDoc, byName);
        }

        /**
         * How many parameters the declaration beginning at {@code from} takes, counted from the
         * source rather than from the doc comment's {@code @param} tags — a comment may document
         * fewer than are declared, and a signature may run over several lines.
         */
        private static int arityAt(String source, int from) {
            int open = source.indexOf('(', from);
            if (open < 0) {
                return -1;
            }
            int depth = 0;
            int params = 0;
            boolean any = false;
            for (int i = open; i < source.length(); i++) {
                char c = source.charAt(i);
                if (c == '(' || c == '<' || c == '[') {
                    depth++;
                } else if (c == ')' || c == '>' || c == ']') {
                    depth--;
                    if (depth == 0) {
                        return any ? params + 1 : 0;
                    }
                } else if (!Character.isWhitespace(c)) {
                    any = true;
                    if (c == ',' && depth == 1) {
                        params++;
                    }
                }
            }
            return -1;
        }

        /** The doc of the member called {@code name} taking {@code arity} parameters, if exactly
         *  one such member is documented. */
        Optional<String> of(String name, int arity) {
            String doc = byName.get(name + "/" + arity);
            if (doc == null) {
                doc = byName.get(name);   // a type or a field, which no arity distinguishes
            }
            return Optional.ofNullable(doc).filter(d -> !d.equals(AMBIGUOUS));
        }

        /** The {@code @param} names of the matching doc comment, in the order they are written —
         *  which is the declaration order the class file has forgotten. */
        List<String> paramsOf(String name, int arity) {
            String doc = of(name, arity).orElse(null);
            if (doc == null) {
                return List.of();
            }
            List<String> params = new ArrayList<>();
            var m = java.util.regex.Pattern.compile("@param\\s+(?!<)(\\w+)").matcher(doc);
            while (m.find()) {
                params.add(m.group(1));
            }
            return params;
        }
    }
}
