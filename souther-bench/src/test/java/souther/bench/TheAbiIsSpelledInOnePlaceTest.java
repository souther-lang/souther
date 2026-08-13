package souther.bench;

import org.junit.jupiter.api.Test;
import souther.compiler.jvm.DecoderKind;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.types.TypeName;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.constantpool.PoolEntry;
import java.lang.classfile.constantpool.StringEntry;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Nothing outside {@code souther.compiler.jvm} assembles the name of a class this compiler invents.
 *
 * <p>The guarantee this backs up is held by the type system, not by this test: a
 * {@link souther.compiler.jvm.JvmClassName} can only be made inside that package, so no reader can
 * produce a generated-class identity of its own. What the type system cannot stop is a caller
 * building a plain {@code String} that happens to be one of those names and handing it to a class
 * loader or an {@code equals}. That is what this looks for, and it is a tripwire rather than the
 * invariant: it does not have to be complete to be worth having.
 *
 * <p>It reads the constant pool rather than the source, because a joint is visible there and prose is
 * not. {@code module + "." + member.name() + "Case"} compiles to a string-concatenation recipe in
 * which every argument stands as U+0001, so the recipe holds a {@code Case} with a joint right before
 * it and a sentence that merely says the word Case does not. So
 * the general words this ABI uses can be looked for without catching every diagnostic that mentions
 * them.
 *
 * <p>The spellings are not listed here. They are asked of the ABI — the difference between what a
 * derived class is called and what it is derived from is the suffix, whatever the suffix currently is
 * — so a naming scheme changed there does not leave this looking for the old one.
 *
 * <p>It lives in the last module the reactor builds, because it reads every module's classes and they
 * have to be there. The module list is asserted, so a reactor reordered later cannot quietly shrink
 * what is covered.
 */
class TheAbiIsSpelledInOnePlaceTest {

    /** Everything whose main classes this covers. */
    private static final List<String> MODULES = List.of(
            "souther-runtime", "souther-syntax", "souther-fmt", "souther-compiler",
            "souther-lsp", "souther-cli", "souther-bench");

    /** What a string-concatenation recipe stands each argument as, so a joint in an assembled name is
     *  visible where a word in a sentence is not. */
    private static final String JOINT = "\u0001";

    /** The other recipe placeholder: a constant folded into the recipe stands as U+0002. */
    private static final String CONSTANT_JOINT = "\u0002";

    /** The one package that may spell these names. */
    private static final String ABI_PACKAGE = "souther.compiler.jvm.";

    /** The one test that may write a generated class's name out, because holding the ABI to its
     *  spellings is what it is for. Everything else asks. */
    private static final String THE_CONTRACT_TEST = "souther.compiler.jvm.SoutherJvmAbiTest";

    @Test
    void noMainClassOutsideTheAbiAssemblesAGeneratedClassName() {
        // What the spellings are is stated in the contract test, not here. This only needs to know
        // that there are some and what they look like now.
        Set<String> spellings = abiSpellings();
        assertFalse(spellings.isEmpty(), "the ABI adds nothing to any name, which cannot be right");
        assertFalse(spellings.contains(""), "a kind of class whose name is its base: " + spellings);

        List<String> violations = new ArrayList<>();
        List<String> scanned = new ArrayList<>();
        for (String module : MODULES) {
            for (String where : List.of("target/classes", "target/test-classes")) {
                Path classes = repoRoot().resolve(module).resolve(where);
                if (where.endsWith("test-classes") && !Files.isDirectory(classes)) {
                    continue;   // a module with no tests of its own
                }
                assertTrue(Files.isDirectory(classes),
                        module + " has no built classes: this test covers what has been built, so a"
                                + " module that has not been is a hole rather than a pass");
                walk(classes, violations, spellings);
            }
            scanned.add(module);
        }
        assertEquals(MODULES, scanned, "every module was read");
        assertTrue(violations.isEmpty(),
                "a generated class's name is assembled outside " + ABI_PACKAGE + ":\n"
                        + String.join("\n", violations));
    }

    /** The control: the shape this looks for is a shape it can find. Without it an emptied scan and a
     *  clean tree read the same. */
    @Test
    void andTheScanWouldSeeOneIfItWereThere() {
        Set<String> spellings = abiSpellings();
        // Built from a spelling the ABI gave, so this control cannot drift from what is looked for —
        // and this class holds no name of its own to be caught by.
        String spelling = spellings.iterator().next();
        assertTrue(offends(JOINT + "." + JOINT + spelling, spellings), "a joint before a spelling");
        assertTrue(offends("bench.runtime." + JOINT + spelling, spellings), "and one in the middle");
        assertFalse(offends("a diagnostic mentioning Result and Case", spellings),
                "prose using the same words is not a joint");
        assertFalse(offends("demo.Quote", spellings), "nor is a name with no spelling in it");
    }

    /**
     * What this ABI adds to a name, asked of the ABI. A derived class is its base plus a suffix, and a
     * module-level one is the module plus a suffix, so the difference is the spelling in both cases.
     */
    private static Set<String> abiSpellings() {
        TypeName x = new TypeName("m", "X");
        GeneratedClass.Value value = new GeneratedClass.Value(x);
        Set<String> out = new LinkedHashSet<>();
        out.add(beyond(new GeneratedClass.BehaviorImpl("m", "x"),
                new GeneratedClass.BehaviorInterface("m", "x")));
        out.add(beyond(new GeneratedClass.BehaviorResult("m", "x"),
                new GeneratedClass.BehaviorInterface("m", "x")));
        out.add(beyond(new GeneratedClass.BridgeCase("m", new TypeName("n", "X")), value));
        out.add(beyond(new GeneratedClass.Encoder(value), value));
        for (DecoderKind kind : DecoderKind.values()) {
            out.add(beyond(new GeneratedClass.Decoder(value, kind), value));
        }
        out.add(beyond(new GeneratedClass.Ctfe(value), value));
        out.add(beyond(new GeneratedClass.ExampleFake(value), value));
        out.add(afterTheModule(new GeneratedClass.ModuleDeclarations("m")));
        out.add(afterTheModule(new GeneratedClass.Helpers("m")));
        // A lambda is numbered, and the number is not part of the spelling.
        out.add(afterTheModule(new GeneratedClass.Lambda("m", 0)).replaceAll("\\d+$", ""));
        return out;
    }

    private static String beyond(GeneratedClass derived, GeneratedClass base) {
        String name = SoutherJvmAbi.nameOf(derived).binaryName();
        String of = SoutherJvmAbi.nameOf(base).binaryName();
        assertTrue(name.startsWith(of), name + " is not " + of + " with something after it");
        return name.substring(of.length());
    }

    /**
     * What a module-level class adds to its module — the dot included.
     *
     * <p>The dot is part of it because of how such a name is assembled when it is assembled by hand:
     * {@code module + ".$Fns"} puts the joint before the dot, not before the {@code $}. Stripping the
     * dot here left the scan looking for something no recipe holds, and two of these went unseen.
     */
    private static String afterTheModule(GeneratedClass generated) {
        return SoutherJvmAbi.nameOf(generated).binaryName().substring("m".length());
    }

    private static boolean offends(String constant, Set<String> spellings) {
        for (String spelling : spellings) {
            if (constant.contains(JOINT + spelling) || constant.equals(spelling)) {
                return true;
            }
        }
        return false;
    }

    private static void walk(Path classes, List<String> violations, Set<String> spellings) {
        try (Stream<Path> files = Files.walk(classes)) {
            files.filter(p -> p.toString().endsWith(".class")).forEach(p -> read(p, violations, spellings));
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    private static void read(Path file, List<String> violations, Set<String> spellings) {
        byte[] bytes;
        try {
            bytes = Files.readAllBytes(file);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        var model = ClassFile.of().parse(bytes);
        String owner = model.thisClass().asInternalName().replace('/', '.');
        if (owner.startsWith(ABI_PACKAGE) || owner.equals(THE_CONTRACT_TEST)
                || owner.startsWith(THE_CONTRACT_TEST + "$")) {
            return;
        }
        for (PoolEntry entry : model.constantPool()) {
            if (entry instanceof StringEntry s && offends(s.stringValue(), spellings)) {
                violations.add(owner + ": " + visible(s.stringValue()));
            }
        }
    }

    private static String visible(String constant) {
        return constant.replace(JOINT, "{}").replace(CONSTANT_JOINT, "{}");
    }

    /** The tree this module sits in. */
    private static Path repoRoot() {
        return Path.of("").toAbsolutePath().getParent();
    }
}
