package souther.architecture;

import souther.test.RepositoryLayout;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.constantpool.MemberRefEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Who may make a machine, and out of whose allowance.
 *
 * <p>Which strings a rule about a position admits is a question with one owner: the reading that
 * answers for that position builds it, once, out of what the position is allowed, and what crosses
 * into every later reader is the set. A reader that builds one itself is a second answer to what
 * the model admits there — and because it would be building under an allowance of its own, the two
 * can differ over a pattern one of them can afford and the other cannot, with neither saying so.
 *
 * <p><b>Three allowances and three owners, which is the shape rather than three numbers.</b> The
 * numbers are equal today and that is a coincidence; what is not a coincidence is which question
 * each of them bounds. One is what a position may build to answer what it admits; one is what
 * writing a value out of a pattern may cost, which is a witness for a row and no answer about any
 * position; one is what walking a published set for where it stops may cost, which is a report's
 * question about an answer somebody else built. Each is named by its owner and by nobody else, so a
 * fourth reader wanting a machine has to say whose allowance it is spending.
 *
 * <p>Read off the compiled classes and not the source, so that a name reached through a constant is
 * a row here whatever it is spelled as. A row that is new is a finding: either the capability moved
 * and this is where it is written down, or something has grown an allowance of its own.
 */
class WhoMayBuildALanguageAboutAPositionTest {

    private static final String BUDGET = "souther/compiler/regex/PatternPlan$Budget";

    private static final String PLAN = "souther/compiler/regex/PatternPlan";

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    /**
     * What a position may build to answer what its rules leave it, named where a compilation
     * grants it and nowhere else.
     *
     * <p>{@code Front.Reading} is where a compilation sets what a reading is governed by, and this
     * figure is one of those: the reading is handed the allowance made out of it and reaches no
     * figure of its own. A second namer is a second grant, and the two are one number only until
     * somebody changes one.
     */
    private static final List<String> OF_ADMITTED_VALUES =
            List.of("souther/compiler/query/Front$Reading");

    /**
     * What writing one value out of a pattern may cost.
     *
     * <p>Its own because it bounds a different question: a caller here is offering a string for a
     * row and has no answer about a position to compose. Where it runs out, no row is offered —
     * which is what it does for a pattern it cannot read either, so nothing about a model turns on
     * the number.
     */
    private static final List<String> OF_A_WITNESS =
            List.of("souther/compiler/partition/Partitions");

    /**
     * What walking a set for where it stops on the order may cost.
     *
     * <p>A report's question about an answer already published, so it is paid for out of an
     * allowance of the report's. Charged to the position instead, a diagnostic would decide what
     * the model is read to admit; and the set it walks is the position's, so nothing here is a
     * second answer about the model.
     */
    private static final List<String> OF_AN_ORDERED_EXTENT =
            List.of("souther/compiler/values/TextExtents");

    /**
     * And who turns a plan into a machine at all, which is the capability the three allowances are
     * about.
     *
     * <p>{@code Realizer} is what a position's answer is built by, and the witness is the one
     * caller that builds a machine to write a value out of rather than to answer with. Everything
     * else takes what one of them left.
     */
    private static final List<String> BUILDS_A_MACHINE = List.of(
            "souther/compiler/partition/Partitions",
            "souther/compiler/values/Realizer");

    @Test
    void whatAPositionMayBuildIsNamedByTheAllowanceAndByNobodyElse() {
        assertEquals(OF_ADMITTED_VALUES, namingTheBudget("OF_ADMITTED_VALUES"),
                "one allowance per position, granted in one place: a second namer of it is a"
                        + " second answer to how much a position may build");
    }

    @Test
    void whatAWitnessMayCostIsNamedByWhoeverWritesOne() {
        assertEquals(OF_A_WITNESS, namingTheBudget("OF_A_WITNESS"),
                "a value pasted into a row is not an answer about a position, and the reverse is"
                        + " what naming this budget elsewhere would make it");
    }

    @Test
    void whatAnOrderedExtentMayCostIsNamedByWhoeverWalksOne() {
        assertEquals(OF_AN_ORDERED_EXTENT, namingTheBudget("OF_AN_ORDERED_EXTENT"),
                "where a set stops is a report's question about a published answer, and this is the"
                        + " allowance it is asked under");
    }

    @Test
    void everyClassThatTurnsAPlanIntoAMachineIsWrittenDownHere() {
        assertEquals(BUILDS_A_MACHINE, callingCompile(),
                "a machine for what a position admits is made by the position's own realizer, and a"
                        + " caller that makes one elsewhere is answering the same question a second"
                        + " time under an allowance of its own");
    }

    /**
     * The walk reads every module's classes.
     *
     * <p>Asked of the modules the repository has and not of what a build happened to leave: a
     * module whose classes are missing is one whose names this cannot see, and the rows from the
     * rest would match while this answered about fewer modules than it names.
     */
    @Test
    void andEveryModuleTheRepositoryHoldsWasRead() {
        List<String> unbuilt = new ArrayList<>();
        for (Path module : REPOSITORY.modules()) {
            if (!Files.isDirectory(classesOf(module)) && hasMainSources(module)) {
                unbuilt.add(module.getFileName().toString());
            }
        }

        assertEquals(List.of(), unbuilt,
                "a module whose classes are not built is one this walk passes over, and a walk that"
                        + " passes over a module answers about the rest while saying it answers"
                        + " about all of them");
    }

    /**
     * And the walk finds a namer that is there.
     *
     * <p>The rows above are who may name a budget; this is that a name this walk should see is one
     * it does see. Matched on a field nothing names, every list would be empty and equal to an
     * empty expectation.
     */
    @Test
    void andTheWalkSeesANamerThatIsThere() {
        assertTrue(namingTheBudget("OF_A_WITNESS").contains("souther/compiler/partition/Partitions"),
                "the witness names its own budget, so a walk that cannot find it finds nothing");
    }

    /** Every class whose constant pool reaches {@code field} of the budgets. */
    private static List<String> namingTheBudget(String field) {
        return found(entry -> entry instanceof MemberRefEntry member
                && member.owner().name().stringValue().equals(BUDGET)
                && member.name().stringValue().equals(field));
    }

    /** Every class that asks a plan for the machine it names. */
    private static List<String> callingCompile() {
        return found(entry -> entry instanceof MemberRefEntry member
                && member.owner().name().stringValue().equals(PLAN)
                && member.name().stringValue().equals("compile"));
    }

    private static List<String> found(java.util.function.Predicate<PoolEntry> reaching) {
        Set<String> out = new TreeSet<>();
        for (Path module : REPOSITORY.modules()) {
            for (Path each : classesUnder(module)) {
                String reader = internalName(module, each);
                // What a class names of itself is not a reader of anything. The plan declares the
                // budgets and the meter they make, so a row for it would be this walk reporting the
                // owner as its own caller.
                if (reader.equals(PLAN) || reader.startsWith(PLAN + "$")) {
                    continue;
                }
                for (PoolEntry entry : constantPoolOf(each)) {
                    if (reaching.test(entry)) {
                        out.add(reader);
                    }
                }
            }
        }
        return new ArrayList<>(out);
    }

    private static Iterable<PoolEntry> constantPoolOf(Path compiled) {
        try {
            return ClassFile.of().parse(Files.readAllBytes(compiled)).constantPool();
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /** The class's own binary name, taken against the directory it was found under rather than off
     *  the first {@code classes} in the path, which a checkout under one would be. */
    private static String internalName(Path module, Path compiled) {
        String name = classesOf(module).relativize(compiled).toString().replace('\\', '/');
        return name.substring(0, name.length() - ".class".length());
    }

    private static Path classesOf(Path module) {
        return module.resolve("target").resolve("classes");
    }

    /** Whether the module has main sources to have been built from. A module holding only tests or
     *  only a pom leaves no classes and is not one this walk is missing. */
    private static boolean hasMainSources(Path module) {
        return Files.isDirectory(module.resolve("src").resolve("main").resolve("java"));
    }

    private static List<Path> classesUnder(Path module) {
        Path where = classesOf(module);
        if (!Files.isDirectory(where)) {
            return List.of();
        }
        try (Stream<Path> found = Files.walk(where)) {
            return found.filter(p -> p.toString().endsWith(".class")).toList();
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
