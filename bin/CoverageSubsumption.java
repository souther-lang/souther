import java.io.DataInputStream;
import java.io.EOFException;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.stream.Stream;

/**
 * Which test classes ran nothing of their own.
 *
 * <p>Reads what a run under {@code -Pcoverage-by-class} wrote — one agent record per test class
 * under every module's {@code target/coverage-by-class/} — and names the classes whose every probe
 * some other class also hit. Run from the repository root, after that run:
 *
 * <pre>java bin/CoverageSubsumption.java</pre>
 *
 * <p>A probe is a point in a main class's bytecode the agent counts as reached; a test class's
 * coverage is the set of probes reached between the previous class's end and its own. Only classes
 * under a module's {@code target/classes} count, so what a test ran of itself or of another test
 * is left out. Nested classes are folded into their outermost class, which is what one file of
 * test source is.
 *
 * <p>Containment says the branches were run, and no more than that. Two classes can run the same
 * branches and assert different things about what came back, so what is printed is a list of
 * candidates to ask, not a list to delete.
 *
 * <p>Columns, tab-separated and one row per test class:
 * <ul>
 * <li>the class;
 * <li>how many probes it reached;
 * <li>{@code none}, {@code held}, {@code by-others}, or {@code by-population-only}: it reached no
 *     main code at all, some probe is its own, every probe is also some other class's, or every
 *     probe is also some other class's but at least one only a class tagged {@code population}
 *     runs — which a pull request's run leaves out, so in that run this class stands alone;
 * <li>how many classes, this one included, reach its least-shared probe: 1 for a held class, and
 *     2 for one whose every branch is one other class's as well — the nearest thing to a twin;
 * <li>one other class containing this one whole, if there is one, else empty.
 * </ul>
 * Which classes carry the tag is read from the test sources, as the annotation written at class
 * level. The test-support module's classes are not main code but the tests' own furniture, so a
 * class that only reads sources through them reaches nothing here.
 */
public final class CoverageSubsumption {

    private CoverageSubsumption() {
    }

    /** The agent's record format: a header, then blocks each led by one type byte. */
    private static final int BLOCK_HEADER = 0x01;
    private static final int BLOCK_SESSION_INFO = 0x10;
    private static final int BLOCK_EXECUTION_DATA = 0x11;

    /** A main class's probes, numbered into one space shared by every class. */
    private record Probes(int offset, int count) {
    }

    public static void main(String[] args) throws IOException {
        Path root = Path.of("").toAbsolutePath();
        Set<String> mainClasses = mainClasses(root);
        Set<String> population = populationClasses(root);

        Map<String, Probes> probesOf = new HashMap<>();
        int[] next = {0};
        Map<String, BitSet> covered = new TreeMap<>();
        try (Stream<Path> modules = Files.list(root)) {
            for (Path module : modules.toList()) {
                Path dir = module.resolve("target").resolve("coverage-by-class");
                if (!Files.isDirectory(dir)) {
                    continue;
                }
                try (Stream<Path> files = Files.list(dir)) {
                    for (Path file : files.filter(f -> f.toString().endsWith(".exec")).toList()) {
                        String name = file.getFileName().toString();
                        name = name.substring(0, name.length() - ".exec".length());
                        int nested = name.indexOf('$');
                        String outer = nested < 0 ? name : name.substring(0, nested);
                        BitSet bits = covered.computeIfAbsent(outer, k -> new BitSet());
                        read(file, mainClasses, probesOf, next, bits);
                    }
                }
            }
        }

        int[] coverers = new int[next[0]];
        int[] coverersOutsidePopulation = new int[next[0]];
        for (Map.Entry<String, BitSet> entry : covered.entrySet()) {
            boolean inPopulation = population.contains(entry.getKey());
            BitSet bits = entry.getValue();
            for (int i = bits.nextSetBit(0); i >= 0; i = bits.nextSetBit(i + 1)) {
                coverers[i]++;
                if (!inPopulation) {
                    coverersOutsidePopulation[i]++;
                }
            }
        }

        for (Map.Entry<String, BitSet> entry : covered.entrySet()) {
            String test = entry.getKey();
            BitSet bits = entry.getValue();
            boolean inPopulation = population.contains(test);
            String standing;
            int rarest = -1;
            if (bits.isEmpty()) {
                standing = "none";
            } else {
                boolean byOthers = true;
                boolean byOthersOutsidePopulation = true;
                for (int i = bits.nextSetBit(0); i >= 0; i = bits.nextSetBit(i + 1)) {
                    if (coverers[i] < 2) {
                        byOthers = false;
                    }
                    if (coverersOutsidePopulation[i] < (inPopulation ? 1 : 2)) {
                        byOthersOutsidePopulation = false;
                    }
                    if (rarest < 0 || coverers[i] < coverers[rarest]) {
                        rarest = i;
                    }
                }
                standing = !byOthers ? "held"
                        : byOthersOutsidePopulation ? "by-others"
                        : "by-population-only";
            }
            String container = "";
            if (standing.equals("by-others") || standing.equals("by-population-only")) {
                for (Map.Entry<String, BitSet> other : covered.entrySet()) {
                    if (other.getKey().equals(test) || !other.getValue().get(rarest)) {
                        continue;
                    }
                    BitSet difference = (BitSet) bits.clone();
                    difference.andNot(other.getValue());
                    if (difference.isEmpty()) {
                        container = other.getKey();
                        break;
                    }
                }
            }
            String sharedBy = rarest < 0 ? "" : String.valueOf(coverers[rarest]);
            System.out.println(test + "\t" + bits.cardinality() + "\t" + standing + "\t" + sharedBy
                    + "\t" + container);
        }
    }

    /** Every class a module built, named as the agent names it: slashes, no extension. */
    private static Set<String> mainClasses(Path root) throws IOException {
        Set<String> names = new HashSet<>();
        try (Stream<Path> modules = Files.list(root)) {
            for (Path module : modules.toList()) {
                if (module.getFileName().toString().equals("souther-test-support")) {
                    continue;
                }
                Path classes = module.resolve("target").resolve("classes");
                if (!Files.isDirectory(classes)) {
                    continue;
                }
                try (Stream<Path> files = Files.walk(classes)) {
                    files.filter(f -> f.toString().endsWith(".class"))
                            .map(f -> classes.relativize(f).toString())
                            .map(s -> s.substring(0, s.length() - ".class".length()))
                            .map(s -> s.replace(File.separatorChar, '/'))
                            .forEach(names::add);
                }
            }
        }
        return names;
    }

    /** The outermost test classes whose source carries the population tag. */
    private static Set<String> populationClasses(Path root) throws IOException {
        Set<String> names = new HashSet<>();
        try (Stream<Path> modules = Files.list(root)) {
            for (Path module : modules.toList()) {
                Path tests = module.resolve("src").resolve("test").resolve("java");
                if (!Files.isDirectory(tests)) {
                    continue;
                }
                try (Stream<Path> files = Files.walk(tests)) {
                    for (Path file : files.filter(f -> f.toString().endsWith(".java")).toList()) {
                        String source = Files.readString(file);
                        if (!source.contains("@Tag(\"population\")")) {
                            continue;
                        }
                        String relative = tests.relativize(file).toString();
                        relative = relative.substring(0, relative.length() - ".java".length());
                        names.add(relative.replace(File.separatorChar, '.'));
                    }
                }
            }
        }
        return names;
    }

    /** Adds to {@code into} every probe of a main class that {@code file} records as hit. */
    private static void read(Path file, Set<String> mainClasses, Map<String, Probes> probesOf,
            int[] next, BitSet into) throws IOException {
        try (InputStream raw = Files.newInputStream(file);
                DataInputStream in = new DataInputStream(raw)) {
            while (true) {
                int type;
                try {
                    type = in.readUnsignedByte();
                } catch (EOFException end) {
                    return;
                }
                switch (type) {
                    case BLOCK_HEADER -> {
                        in.readChar();
                        in.readChar();
                    }
                    case BLOCK_SESSION_INFO -> {
                        in.readUTF();
                        in.readLong();
                        in.readLong();
                    }
                    case BLOCK_EXECUTION_DATA -> {
                        in.readLong();
                        String name = in.readUTF();
                        boolean[] hit = booleans(in);
                        int count = hit.length;
                        if (!mainClasses.contains(name)) {
                            continue;
                        }
                        Probes probes = probesOf.computeIfAbsent(name, k -> {
                            Probes p = new Probes(next[0], count);
                            next[0] += count;
                            return p;
                        });
                        if (probes.count() != count) {
                            throw new IllegalStateException(
                                    name + " has " + count + " probes in " + file + " and "
                                            + probes.count() + " elsewhere");
                        }
                        for (int i = 0; i < count; i++) {
                            if (hit[i]) {
                                into.set(probes.offset() + i);
                            }
                        }
                    }
                    default -> throw new IllegalStateException(
                            "unknown block " + type + " in " + file);
                }
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /** Seven bits a byte, low first, the high bit saying another byte follows. */
    private static int varInt(DataInputStream in) throws IOException {
        int value = 0;
        for (int shift = 0; ; shift += 7) {
            int b = in.readUnsignedByte();
            value |= (b & 0x7F) << shift;
            if ((b & 0x80) == 0) {
                return value;
            }
        }
    }

    /** Flags eight to a byte, low bit first; their number precedes them. */
    private static boolean[] booleans(DataInputStream in) throws IOException {
        int count = varInt(in);
        boolean[] flags = new boolean[count];
        int buffer = 0;
        for (int i = 0; i < count; i++) {
            if ((i % 8) == 0) {
                buffer = in.readUnsignedByte();
            }
            flags[i] = (buffer & 1) != 0;
            buffer >>>= 1;
        }
        return flags;
    }
}
