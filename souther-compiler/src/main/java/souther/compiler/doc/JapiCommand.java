package souther.compiler.doc;

import souther.compiler.io.BoundedRead;
import souther.compiler.io.ConfinedTree;
import souther.compiler.io.ConfinementException;
import souther.compiler.io.LimitExceededException;
import souther.compiler.io.WorkBudget;
import souther.compiler.jvm.JvmClassName;
import souther.compiler.check.Suggest;

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
import java.lang.constant.ConstantDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;
import java.lang.reflect.AccessFlag;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.LinkOption;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
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

    /** How far a name may be from one on the class path and still be offered as the one that was meant. */
    private static final int NEAR_ENOUGH = 2;

    /** How many names a miss is answered with. */
    private static final int MOST_SUGGESTIONS = 3;

    /** How deep the search for names to suggest walks one directory entry. */
    private static final int DEEPEST_WALK = 32;

    private JapiCommand() {}

    public static int run(String[] args, PrintStream out, PrintStream err) {
        return run(args, out, err, System.getProperty("java.class.path", ""));
    }

    /**
     * The same run, reading only what is under {@code root}: an entry outside it, or a link met on
     * the way to a file, is refused rather than followed. For a caller whose class path is not its
     * own to choose.
     */
    public static int runConfined(String[] args, PrintStream out, PrintStream err, Path root) {
        return runConfined(args, out, err, root, BoundedRead.MOST_ENTRIES_PER_REQUEST);
    }

    /**
     * Where a run reads from: anywhere its caller says, or only under one root.
     *
     * <p>Every path this command opens is made by joining a name onto a class path entry, and the
     * name comes out of the argument, a class file or a jar, so each of them is passed through here
     * on its way to a file. There is no other way to a file in this class.
     */
    private record Disk(ConfinedTree confinedTo) {

        static final Disk OPEN = new Disk(null);

        Path path(Path wanted) throws IOException {
            if (confinedTo == null) {
                return wanted;
            }
            Path root = confinedTo.root();
            Path absolute = wanted.toAbsolutePath().normalize();
            if (!absolute.startsWith(root)) {
                throw new ConfinementException("is not under " + root);
            }
            return absolute.equals(root) ? root : confinedTo.resolve(root.relativize(absolute).toString());
        }

        byte[] read(Path file) throws IOException {
            try (java.io.InputStream in = confinedTo == null
                    ? Files.newInputStream(file) : Files.newInputStream(file, LinkOption.NOFOLLOW_LINKS)) {
                return BoundedRead.bytes(in, BoundedRead.CLASS_FILE_BYTES);
            }
        }
    }

    /**
     * The same run, with a class loader carrying whatever it carries.
     *
     * <p>It is not consulted: a class taken from one copy of a library is not described by another
     * copy this tool happens to hold. The parameter is how a caller says which loader that would
     * have been.
     */
    static int run(String[] args, PrintStream out, PrintStream err, ClassLoader bundled) {
        return run(args, out, err, System.getProperty("java.class.path", ""));
    }

    /** The same run, over the class path to fall back on when the caller names none. */
    static int run(String[] args, PrintStream out, PrintStream err, String defaultClassPath) {
        return run(args, out, err, defaultClassPath, Disk.OPEN, WorkBudget.of(BoundedRead.MOST_ENTRIES_PER_REQUEST));
    }

    /** The same confined run, with {@code mostEntries} as everything one request may look at. */
    static int runConfined(String[] args, PrintStream out, PrintStream err, Path root, long mostEntries) {
        return run(args, out, err, System.getProperty("java.class.path", ""),
                new Disk(ConfinedTree.at(root)), WorkBudget.of(mostEntries));
    }

    /**
     * The same run, reading what the caller names through {@code disk}, and looking at no more than
     * {@code work} allows in all. The class path to fall back on is this command's own and is read
     * from wherever it is.
     */
    private static int run(String[] args, PrintStream out, PrintStream err, String defaultClassPath,
                           Disk disk, WorkBudget work) {
        String name = null;
        List<Entry> entries = new ArrayList<>();
        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case "-cp", "--class-path" -> {
                    if (i + 1 == args.length) {
                        err.println("-cp needs a path");
                        return 2;
                    }
                    for (String p : args[++i].split(java.io.File.pathSeparator)) {
                        entries.add(new Entry(Path.of(p), true, disk, work));
                    }
                }
                default -> name = args[i];
            }
        }
        if (name == null) {
            err.println("usage: souther japi <class-or-package>[#<member>] [-cp <path>]");
            return 2;
        }
        if (entries.isEmpty()) {
            for (String p : defaultClassPath.split(java.io.File.pathSeparator)) {
                if (!p.isEmpty()) {
                    entries.add(new Entry(Path.of(p), false, Disk.OPEN, work));
                }
            }
        }

        String member = null;
        int hash = name.indexOf('#');
        if (hash >= 0) {
            member = name.substring(hash + 1);
            name = name.substring(0, hash);
        }
        if (!isQualifiedName(name)) {
            err.println("`" + name + "` is not a fully qualified class or package name");
            return 2;
        }

        String classPath = entries.stream().map(e -> e.path().toString())
                .collect(java.util.stream.Collectors.joining(java.io.File.pathSeparator));
        Skipped skipped = new Skipped(err, new java.util.HashSet<>());
        Found found = findClass(name, entries, skipped);
        if (found != null) {
            try (ClassLookup lookup = lookupFor(entries)) {
                return print(found, name, member, out, err, classPath, lookup);
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }
        }
        if (member != null) {
            err.println("no class `" + name + "` on the class path:");
            return missed(name, entries, err, skipped);
        }
        List<String> classes = classesUnder(name, entries, skipped);
        if (!classes.isEmpty()) {
            classes.forEach(out::println);
            return 0;
        }
        err.println("no class or package `" + name + "` on the class path:");
        return missed(name, entries, err, skipped);
    }

    /**
     * A class path entry, and whether the caller is the one who named it.
     *
     * <p>A path the caller wrote is theirs, and it is said back as they wrote it — it is what they
     * need to see where the search went. A path this command fell back to is its own hosting, which
     * says nothing a reader can act on and is not theirs to be handed, so it is named by the file it
     * is.
     */
    private record Entry(Path path, boolean given, Disk disk, WorkBudget work) {

        /** This entry's own path, as its disk allows it to be opened. */
        Path file() throws IOException {
            return disk.path(path);
        }

        /** The path {@code relative} names under this entry, as its disk allows it to be opened. */
        Path below(String relative) throws IOException {
            return disk.path(path.resolve(relative));
        }

        /** The path {@code name} names beside this entry, as its disk allows it to be opened. */
        Path beside(String name) throws IOException {
            return disk.path(path.resolveSibling(name));
        }

        /** What this entry is called when a message names it. */
        String shown() {
            Path file = path.getFileName();
            return given || file == null ? path.toString() : file.toString();
        }

        /**
         * Why this entry could not be read.
         *
         * <p>An {@link IOException} names the file it is about, so passing its message on would hand
         * back by another route the path {@link #shown} keeps back. A message belongs to the caller
         * who wrote the path it names; for an entry this command fell back on, the failure is said
         * by what kind of failure it is.
         */
        String failure(IOException e) {
            if (given) {
                return e.getMessage() == null ? e.getClass().getSimpleName() : e.getMessage();
            }
            return switch (e) {
                case java.nio.file.NoSuchFileException _ -> "no such file";
                case java.nio.file.AccessDeniedException _ -> "permission denied";
                case java.io.FileNotFoundException _ -> "cannot be opened";
                case java.util.zip.ZipException _ -> "not a readable archive";
                default -> "cannot be read";
            };
        }
    }

    /**
     * Where the search went, and the nearest names to the one that was not found.
     *
     * <p>A name out of the class path and a name misspelled read the same, and the compiler answers
     * the second for every identifier in a source file. A reader of a jar has less to go on than the
     * author of a source file, not more.
     */
    private static int missed(String name, List<Entry> entries, PrintStream err, Skipped skipped) {
        entries.forEach(e -> err.println("  " + e.shown()));
        List<String> near = Suggest.nearest(name, namesOn(entries, skipped), NEAR_ENOUGH, MOST_SUGGESTIONS);
        if (!near.isEmpty()) {
            err.println("did you mean: " + String.join(", ", near));
        }
        return 2;
    }

    /**
     * Every top-level class the class path holds, and the packages holding them — the names a miss
     * could have meant.
     *
     * <p>Only entry names are read. Whether a class is published is what {@link #classesUnder}
     * settles by parsing it, and parsing every class on the class path to phrase one guess would
     * cost more than the guess is worth.
     */
    private static List<String> namesOn(List<Entry> entries, Skipped skipped) {
        List<String> names = new ArrayList<>();
        for (Entry entry : entries) {
            try {
                Path at = entry.file();
                if (Files.isDirectory(at)) {
                    try (var files = Files.walk(at, DEEPEST_WALK)) {
                        for (Iterator<Path> walked = files.iterator(); walked.hasNext();) {
                            Path f = walked.next();
                            entry.work().spend(1);
                            if (Files.isRegularFile(f)) {
                                add(names, at.relativize(f).toString().replace(java.io.File.separatorChar, '/'));
                            }
                        }
                    }
                } else if (Files.isRegularFile(at)) {
                    try (JarFile jar = openJar(entry, at); var all = jar.versionedStream()) {
                        for (Iterator<JarEntry> listed = all.iterator(); listed.hasNext();) {
                            entry.work().spend(1);
                            add(names, listed.next().getName());
                        }
                    }
                }
            } catch (IOException e) {
                skipped.report(entry, e);
            } catch (UncheckedIOException e) {
                // A walk opens the directory it was handed straight away and every directory under
                // it only on reaching it, so a failure below the entry arrives here rather than
                // above. What was walked before it is kept: a name to suggest may already be among
                // them, and looking for one is not what may end the run.
                skipped.report(entry, e.getCause());
            }
        }
        return names.stream().distinct().toList();
    }

    /** The binary name {@code resource} declares, and its package, when it declares a type. */
    private static void add(List<String> names, String resource) {
        int slash = resource.lastIndexOf('/');
        String simple = topLevelName(resource.substring(slash + 1));
        if (simple == null) {
            return;
        }
        String pkg = slash < 0 ? "" : resource.substring(0, slash).replace('/', '.');
        names.add(pkg.isEmpty() ? simple : pkg + "." + simple);
        if (!pkg.isEmpty()) {
            names.add(pkg);
        }
    }

    /** A class's bytes and the classpath entry they came from — kept together because the
     *  sources jar, and with it the javadoc, is found from the entry. */
    private record Found(byte[] bytes, Entry entry) {}

    /** A dotted run of Java identifiers. The name becomes a path under each class path entry, so a
     *  `..` segment, a separator or an empty segment would reach outside it. */
    private static boolean isQualifiedName(String name) {
        if (name.isEmpty()) {
            return false;
        }
        for (String segment : name.split("\\.", -1)) {
            if (segment.isEmpty() || !Character.isJavaIdentifierStart(segment.codePointAt(0))
                    || !segment.codePoints().allMatch(Character::isJavaIdentifierPart)) {
                return false;
            }
        }
        return true;
    }

    private static Found findClass(String binaryName, List<Entry> entries, Skipped skipped) {
        String resource = JvmClassName.classFile(binaryName);
        for (Entry entry : entries) {
            try {
                Path path = entry.file();
                if (Files.isDirectory(path)) {
                    Path f = entry.below(resource);
                    if (Files.isRegularFile(f)) {
                        return new Found(entry.disk().read(f), entry);
                    }
                } else if (Files.isRegularFile(path)) {
                    try (JarFile jar = openJar(entry, path)) {
                        ZipEntry e = jar.getEntry(resource);
                        if (e != null) {
                            return new Found(jarEntryBytes(jar, e, BoundedRead.CLASS_FILE_BYTES), entry);
                        }
                    }
                }
            } catch (IOException e) {
                skipped.report(entry, e);
            }
        }
        return null;
    }

    /**
     * Where an entry that cannot be opened is reported.
     *
     * <p>A class path is given, not chosen: one entry that cannot be opened is said and stepped over,
     * so the entries beside it still answer. A miss walks the class path once for the class, once for
     * the package and once for a name to suggest, and the same entry fails all three — so what has
     * been said is remembered, and a reader is told once.
     */
    private record Skipped(PrintStream err, Set<String> said) {

        void report(Entry entry, IOException e) {
            String line = "skipping `" + entry.shown() + "`: " + entry.failure(e);
            if (said.add(line)) {
                err.println(line);
            }
        }
    }

    /**
     * The published top-level types of {@code packageName}.
     *
     * <p>A class file's name says nothing about whether anyone outside its package may name the
     * type. This command answers a dependency's public API, so the class's own access flag decides,
     * and {@code package-info} — a descriptor rather than a type — is left out with it.
     */
    private static List<String> classesUnder(String packageName, List<Entry> entries, Skipped skipped) {
        String prefix = packageName.replace('.', '/') + "/";
        List<String> classes = new ArrayList<>();
        for (Entry entry : entries) {
            try {
                Path path = entry.file();
                if (Files.isDirectory(path)) {
                    String packageDirectory = packageName.replace('.', '/');
                    Path dir = entry.below(packageDirectory);
                    if (Files.isDirectory(dir)) {
                        List<String> names = new ArrayList<>();
                        try (var files = Files.list(dir)) {
                            for (Iterator<Path> listed = files.iterator(); listed.hasNext();) {
                                entry.work().spend(1);
                                names.add(listed.next().getFileName().toString());
                            }
                        }
                        for (String fileName : names) {
                            String simple = topLevelName(fileName);
                            if (simple != null
                                    && isPublic(entry.disk().read(entry.below(packageDirectory + "/" + fileName)))) {
                                classes.add(packageName + "." + simple);
                            }
                        }
                    }
                } else if (Files.isRegularFile(path)) {
                    try (JarFile jar = openJar(entry, path)) {
                        List<JarEntry> underPackage = new ArrayList<>();
                        try (var all = jar.versionedStream()) {
                            for (Iterator<JarEntry> listed = all.iterator(); listed.hasNext();) {
                                entry.work().spend(1);
                                JarEntry e = listed.next();
                                if (e.getName().startsWith(prefix)) {
                                    underPackage.add(e);
                                }
                            }
                        }
                        for (JarEntry e : underPackage) {
                            String simple = topLevelName(e.getName().substring(prefix.length()));
                            if (simple == null || simple.contains("/")) {
                                continue;
                            }
                            if (isPublic(jarEntryBytes(jar, e, BoundedRead.CLASS_FILE_BYTES))) {
                                classes.add(packageName + "." + simple);
                            }
                        }
                    }
                }
            } catch (IOException e) {
                skipped.report(entry, e);
            }
        }
        return classes.stream().distinct().sorted().toList();
    }

    /**
     * The lookup javac resolves types through when every entry is confined, or {@code null} when the
     * class path is the caller's own and javac may search it itself.
     *
     * <p>A class path string handed to javac is searched with javac's own file access, which follows
     * a link inside an entry however the entry was checked. So a confined run gives javac no class
     * path: it asks for one package at a time and is answered from the same entries, read the same
     * way as every other file of the run.
     */
    private static ClassLookup lookupFor(List<Entry> entries) {
        if (entries.stream().anyMatch(e -> e.disk().confinedTo() == null)) {
            return null;
        }
        return new EntryClasses(entries);
    }

    /**
     * The classes of one request's entries, by package.
     *
     * <p>javac asks for one package at a time, as many times as the source names packages, and a
     * source is somebody else's text. Every question answered by looking through an archive again
     * would make the cost of a request the number of packages named times the size of the archive.
     * So an archive is opened once, kept open for as long as this lives, and listed once into an
     * index of its classes by package; after that a package is answered from the index and a class
     * is read from the archive that is already open. The listing is spent from the request's budget
     * like every other look at an entry, and so is what it holds in memory.
     */
    private static final class EntryClasses implements ClassLookup {

        private final List<Entry> entries;
        private final Map<Path, JarFile> jars = new HashMap<>();
        private final Map<Path, Map<String, List<String>>> indexes = new HashMap<>();

        /** An archive that could not be opened or listed, so the question is not asked of it again. */
        private final Map<Path, IOException> unreadable = new HashMap<>();

        EntryClasses(List<Entry> entries) {
            this.entries = entries;
        }

        @Override
        public List<Held> classesIn(String packageName) {
            List<Held> held = new ArrayList<>();
            for (Entry entry : entries) {
                try {
                    held.addAll(heldBy(entry, packageName));
                } catch (IOException _) {
                    // An entry that cannot be read holds no classes, as it does for the search.
                }
            }
            return held;
        }

        @Override
        public void close() throws IOException {
            IOException failed = null;
            for (JarFile jar : jars.values()) {
                try {
                    jar.close();
                } catch (IOException e) {
                    failed = e;
                }
            }
            jars.clear();
            if (failed != null) {
                throw failed;
            }
        }

        private List<Held> heldBy(Entry entry, String packageName) throws IOException {
            String directory = packageName.replace('.', '/');
            Path at = entry.file();
            List<Held> held = new ArrayList<>();
            if (Files.isDirectory(at)) {
                Path dir = directory.isEmpty() ? at : entry.below(directory);
                if (!Files.isDirectory(dir)) {
                    return held;
                }
                try (var files = Files.list(dir)) {
                    for (Iterator<Path> listed = files.iterator(); listed.hasNext();) {
                        entry.work().spend(1);
                        String name = listed.next().getFileName().toString();
                        if (isClassFile(name)) {
                            String relative = directory.isEmpty() ? name : directory + "/" + name;
                            held.add(new Held(binaryNameOf(packageName, name),
                                    () -> entry.disk().read(entry.below(relative))));
                        }
                    }
                }
            } else if (Files.isRegularFile(at)) {
                for (String name : indexOf(entry, at).getOrDefault(directory, List.of())) {
                    String resource = directory.isEmpty() ? name : directory + "/" + name;
                    held.add(new Held(binaryNameOf(packageName, name), () -> bytesOf(entry, at, resource)));
                }
            }
            return held;
        }

        private JarFile jarOf(Entry entry, Path at) throws IOException {
            JarFile jar = jars.get(at);
            if (jar == null) {
                jar = openJar(entry, at);
                jars.put(at, jar);
            }
            return jar;
        }

        private Map<String, List<String>> indexOf(Entry entry, Path at) throws IOException {
            IOException before = unreadable.get(at);
            if (before != null) {
                throw before;
            }
            Map<String, List<String>> index = indexes.get(at);
            if (index != null) {
                return index;
            }
            try {
                index = new HashMap<>();
                try (var all = jarOf(entry, at).versionedStream()) {
                    for (Iterator<JarEntry> listed = all.iterator(); listed.hasNext();) {
                        entry.work().spend(1);
                        String name = listed.next().getName();
                        int slash = name.lastIndexOf('/');
                        String fileName = name.substring(slash + 1);
                        if (isClassFile(fileName)) {
                            index.computeIfAbsent(slash < 0 ? "" : name.substring(0, slash),
                                    _ -> new ArrayList<>()).add(fileName);
                        }
                    }
                }
            } catch (IOException e) {
                unreadable.put(at, e);
                throw e;
            }
            indexes.put(at, index);
            return index;
        }

        private byte[] bytesOf(Entry entry, Path at, String resource) throws IOException {
            JarFile jar = jarOf(entry, at);
            ZipEntry found = jar.getEntry(resource);
            if (found == null) {
                throw new java.io.FileNotFoundException(resource);
            }
            return jarEntryBytes(jar, found, BoundedRead.CLASS_FILE_BYTES);
        }
    }

    /**
     * An archive opened at the version this JVM runs at, having spent its number of entries from
     * the request's budget. Opening one reads its whole directory, so what a request opens counts
     * as looking at it even when it then asks for a single entry.
     */
    private static JarFile openJar(Entry entry, Path at) throws IOException {
        JarFile jar = versioned(at);
        try {
            entry.work().spend(jar.size());
        } catch (LimitExceededException e) {
            jar.close();
            throw e;
        }
        return jar;
    }

    private static boolean isClassFile(String fileName) {
        return fileName.endsWith(".class") && !fileName.equals("module-info.class");
    }

    private static String binaryNameOf(String packageName, String classFileName) {
        String simple = classFileName.substring(0, classFileName.length() - ".class".length());
        return packageName.isEmpty() ? simple : packageName + "." + simple;
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
                             PrintStream err, String classPath, ClassLookup lookup) {
        ClassModel cm = ClassFile.of().parse(found.bytes());
        String simpleName = binaryName.substring(binaryName.lastIndexOf('.') + 1);
        // A constructor is named for its own type. `Outer$Inner` is how the class file spells the
        // type, and `Inner` is what the source calls the constructor.
        String constructorName = simpleName.substring(simpleName.lastIndexOf('$') + 1);
        String source = sourceOf(found.entry(), binaryName);
        SourceDoc doc = source == null ? SourceDoc.NONE : SourceDoc.of(source, binaryName, classPath, lookup);
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
            doc.ofField(name).ifPresent(d -> body.append(indent(d)).append("\n"));
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
            String shown = methodName.equals("<init>") ? constructorName : methodName;
            members.add(shown);
            if (member != null && !member.equals(shown)) {
                continue;
            }
            body.append("\n");
            doc.ofMethod(shown, m.methodTypeSymbol()).ifPresent(d -> body.append(indent(d)).append("\n"));
            body.append("  ").append(methodLine(m, constructorName, doc)).append("\n");
        }
        if (member != null && body.isEmpty()) {
            err.println("`" + binaryName + "` has no public member `" + member + "`");
            err.println("members: " + String.join(", ", members.stream().distinct().toList()));
            return 2;
        }
        if (member == null) {
            doc.classDoc().ifPresent(d -> out.println(indent(d).stripIndent()));
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
        return memberFlags(f.flags().flags()) + type + " " + f.fieldName().stringValue() + value(f);
    }

    /**
     * {@code  = <literal>} for a field the class file carries the value of, and nothing for one it
     * does not.
     *
     * <p>A constant's value is the whole of what its declaration says, and a reader comparing it
     * against what some other code produces needs the value rather than the name. Only a compile-time
     * constant has one in the class file; a field an initializer computes has none, and none is
     * invented for it.
     */
    private static String value(FieldModel f) {
        return f.findAttribute(Attributes.constantValue())
                .map(a -> " = " + literal(a.constant().constantValue(), f.fieldTypeSymbol()))
                .orElse("");
    }

    /**
     * A constant written as Java writes it.
     *
     * <p>The pool stores {@code boolean} and {@code char} as an int and says nothing about the width
     * of an integer, so the field's own descriptor is what tells them apart.
     *
     * <p>Three floating-point values have no literal that spells them, and Java names them on
     * {@code Float} and {@code Double} instead. A name is what is printed for them: what japi prints
     * is read as Java, and {@code NaNf} — which is what a disassembler says — is not.
     */
    private static String literal(ConstantDesc value, ClassDesc type) {
        if (value instanceof String s) {
            return quoted(s, '"');
        }
        if (type.equals(ConstantDescs.CD_boolean)) {
            return ((Integer) value) == 0 ? "false" : "true";
        }
        if (type.equals(ConstantDescs.CD_char)) {
            return quoted(Character.toString((char) (int) (Integer) value), '\'');
        }
        return switch (value) {
            case Long l -> l + "L";
            case Float f when f.isNaN() || f.isInfinite() -> "Float." + named(f.isNaN(), f > 0);
            case Double d when d.isNaN() || d.isInfinite() -> "Double." + named(d.isNaN(), d > 0);
            case Float f -> f + "f";
            default -> String.valueOf(value);
        };
    }

    /** What Java calls a floating-point value no literal spells. */
    private static String named(boolean notANumber, boolean above) {
        return notANumber ? "NaN" : above ? "POSITIVE_INFINITY" : "NEGATIVE_INFINITY";
    }

    /** {@code text} between {@code quote}s, with what Java cannot write plainly escaped. */
    private static String quoted(String text, char quote) {
        StringBuilder sb = new StringBuilder().append(quote);
        text.codePoints().forEach(c -> sb.append(switch (c) {
            case '\\' -> "\\\\";
            case '\b' -> "\\b";
            case '\f' -> "\\f";
            case '\n' -> "\\n";
            case '\r' -> "\\r";
            case '\t' -> "\\t";
            default -> c == quote ? "\\" + quote
                    : c < 0x20 || c == 0x7f ? String.format("\\u%04x", c)
                    : new String(Character.toChars(c));
        }));
        return sb.append(quote).toString();
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
        List<String> names = paramNames(m, paramTypes.size(), doc.paramsOf(shown, mt));
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

    private static List<String> paramNames(MethodModel m, int count, List<String> declared) {
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
            // about which String is the code and which the message. The source declared them in an
            // order, and that order is theirs.
            if (name == null && declared.size() == count) {
                name = declared.get(i);
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

    /** The comment's own text, put back into the shape it was written in. */
    private static String indent(String comment) {
        StringBuilder sb = new StringBuilder("  /**");
        comment.lines().forEach(l -> sb.append("\n   * ").append(l.strip()));
        return sb.append("\n   */").toString();
    }

    // ---- the source a type was written in ----

    /**
     * The source of the file {@code binaryName} is declared in, taken only from the artifact the
     * class itself was read from: the {@code -sources.jar} beside it, or sources carried inside it.
     *
     * <p>Sources carried inside are what the ordinary invocation needs, since the CLI is one shaded
     * jar with its dependencies inside it and nothing beside it. They are read out of that same jar
     * rather than off this tool's class path, because the two are not the same question — a class
     * taken from some other copy of a library must not be described by the copy this tool happens
     * to carry.
     */
    private static String sourceOf(Entry entry, String binaryName) {
        String path = binaryName.split("\\$")[0].replace('.', '/') + ".java";
        String beside = besideJar(entry, path);
        return beside != null ? beside : carriedInside(entry, "META-INF/souther-sources/" + path);
    }

    private static String besideJar(Entry entry, String path) {
        String file = entry.path().getFileName().toString();
        if (!file.endsWith(".jar")) {
            return null;
        }
        try {
            return readFrom(entry, entry.beside(file.substring(0, file.length() - 4) + "-sources.jar"), path);
        } catch (ConfinementException _) {
            return null;   // a sources jar this run may not open is a jar that has no sources
        } catch (IOException ex) {
            throw new UncheckedIOException(ex);
        }
    }

    private static String carriedInside(Entry entry, String path) {
        try {
            return readFrom(entry, entry.file(), path);
        } catch (ConfinementException _) {
            return null;
        } catch (IOException ex) {
            throw new UncheckedIOException(ex);
        }
    }

    private static String readFrom(Entry entry, Path jar, String path) throws IOException {
        if (!Files.isRegularFile(jar) || !jar.getFileName().toString().endsWith(".jar")) {
            return null;
        }
        try (JarFile open = openJar(entry, jar)) {
            ZipEntry e = open.getEntry(path);
            return e == null ? null
                    : new String(jarEntryBytes(open, e, BoundedRead.SOURCE_FILE_BYTES), StandardCharsets.UTF_8);
        } catch (LimitExceededException _) {
            return null;   // a source larger than a run reads is not read
        }
    }

    private static byte[] jarEntryBytes(JarFile jar, ZipEntry entry, long mostBytes) throws IOException {
        try (java.io.InputStream in = jar.getInputStream(entry)) {
            return BoundedRead.bytes(in, mostBytes);
        }
    }
}
