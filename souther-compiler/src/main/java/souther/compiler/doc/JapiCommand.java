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
                    try (JarFile jar = new JarFile(entry.toFile())) {
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

    private static List<String> classesUnder(String packageName, List<Path> entries, PrintStream err) {
        String prefix = packageName.replace('.', '/') + "/";
        List<String> classes = new ArrayList<>();
        for (Path entry : entries) {
            try {
                if (Files.isDirectory(entry)) {
                    Path dir = entry.resolve(packageName.replace('.', '/'));
                    if (Files.isDirectory(dir)) {
                        try (var files = Files.list(dir)) {
                            files.map(f -> f.getFileName().toString())
                                    .filter(f -> f.endsWith(".class") && !f.contains("$"))
                                    .forEach(f -> classes.add(packageName + "." + f.substring(0, f.length() - 6)));
                        }
                    }
                } else if (Files.isRegularFile(entry)) {
                    try (JarFile jar = new JarFile(entry.toFile())) {
                        jar.stream().map(ZipEntry::getName)
                                .filter(n -> n.startsWith(prefix) && n.endsWith(".class"))
                                .map(n -> n.substring(prefix.length(), n.length() - 6))
                                .filter(n -> !n.contains("/") && !n.contains("$"))
                                .forEach(n -> classes.add(packageName + "." + n));
                    }
                }
            } catch (IOException e) {
                unreadable(entry, e, err);
            }
        }
        return classes.stream().sorted().toList();
    }

    // ---- rendering ----

    private static int print(Found found, String binaryName, String member, PrintStream out,
                             PrintStream err, ClassLoader bundled) {
        ClassModel cm = ClassFile.of().parse(found.bytes());
        SourceDoc doc = SourceDoc.of(found.entry(), binaryName, bundled);
        String simpleName = binaryName.substring(binaryName.lastIndexOf('.') + 1);

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
            doc.of(name).ifPresent(d -> body.append(indent(d)).append("\n"));
            body.append("  ").append(fieldLine(f, doc)).append("\n");
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
            doc.of(shown).ifPresent(d -> body.append(indent(d)).append("\n"));
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

    private static String fieldLine(FieldModel f, SourceDoc doc) {
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
        List<String> names = paramNames(m, paramTypes.size(), doc.paramsOf(shown));
        for (int i = 0; i < paramTypes.size(); i++) {
            if (i > 0) {
                sb.append(", ");
            }
            sb.append(paramTypes.get(i)).append(" ").append(names.get(i));
        }
        return sb.append(")").toString();
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
         * The javadoc for {@code binaryName}, from the {@code -sources.jar} beside the jar it was
         * read from, or failing that from sources bundled with this tool.
         *
         * <p>The bundled copy is what the common invocation needs: the CLI is one shaded jar with
         * its dependencies inside it and nothing beside it, so a sibling lookup finds nothing and
         * the javadoc this command promises would never appear.
         */
        static SourceDoc of(Path entry, String binaryName, ClassLoader bundled) {
            String outermost = binaryName.split("\\$")[0];
            String simpleName = outermost.substring(outermost.lastIndexOf('.') + 1);
            String path = outermost.replace('.', '/') + ".java";

            String source = besideJar(entry, path);
            if (source == null) {
                source = fromBundle(bundled, path);
            }
            return source == null ? NONE : parse(source, simpleName);
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

        private static String fromBundle(ClassLoader bundled, String path) {
            if (bundled == null) {
                return null;
            }
            try (java.io.InputStream in = bundled.getResourceAsStream("META-INF/souther-sources/" + path)) {
                return in == null ? null : new String(in.readAllBytes(), StandardCharsets.UTF_8);
            } catch (IOException ex) {
                throw new UncheckedIOException(ex);
            }
        }

        static SourceDoc parse(String source, String simpleName) {
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
                    byName.putIfAbsent(named.group(2), doc);
                }
            }
            return new SourceDoc(classDoc, byName);
        }

        Optional<String> of(String name) {
            return Optional.ofNullable(byName.get(name));
        }

        /** The {@code @param} names of {@code name}'s doc comment, in the order they are written —
         *  which is the declaration order the class file has forgotten. */
        List<String> paramsOf(String name) {
            String doc = byName.get(name);
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
