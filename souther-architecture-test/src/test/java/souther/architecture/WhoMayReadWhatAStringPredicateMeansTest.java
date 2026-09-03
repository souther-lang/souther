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
 * Who may read what a predicate over a string means.
 *
 * <p>A rule tells the strings it admits from the rest, and that is a fact about a language. Whether
 * the position the rule is about is divided, restricted, or left where it was found is a different
 * fact, answered by what the rule is written in — and a reader that derives the second from the
 * first is deciding a question it does not own. That is what happened: the walk that draws lines
 * read the predicate a second time, called the two sides of the language two classes of the
 * position, and published "the model divides this position into values this measure draws no line
 * between" of a declaration that refuses to build anything on the other side.
 *
 * <p>So the edge is what is checked, and not the sentence that came out of it. Renaming the reason
 * closes one occurrence; what closes the shape is that nothing between the predicate's reading and
 * a word about a position exists to be used again. The reading that turns clauses into sets is the
 * one owner, and every later reader takes what it settled.
 *
 * <p>Read off the compiled classes and not off the source, so that an intermediary put between the
 * two — a class named for anything at all, holding what the language came to — arrives here as a
 * row. A walk over spellings would find the words a reader chose and not the edge it built.
 *
 * <p>Its own tests are not read. A test builds a reading to look at it and publishes nothing, and a
 * list that moved whenever one was written is a list nobody keeps up.
 */
class WhoMayReadWhatAStringPredicateMeansTest {

    private static final String OWNER = "souther/compiler/check/StringPredicates";

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    /**
     * Every class that reads one, and what it reads it for.
     *
     * <p>Two, and each asks a different question of the same table.
     *
     * <p>{@code AdmissibleReading} turns the clause into the strings it admits, which is the one
     * place what a rule means about a position is worked out. Everything a later reader says about
     * the position comes from what this left.
     *
     * <p>{@code Partitions} asks what string would satisfy the rule, which is a witness to paste
     * into a row rather than an answer about the position. A format proposes a value the same way a
     * minimum does, and which of them the whole of the rules admits is settled elsewhere.
     *
     * <p>A row for a class in {@code inputs}, {@code partition} or {@code report} is the edge this
     * exists to refuse: those name what a position came to, and a rule's meaning reaching them
     * except through the values it left is a second answer to a question that has an owner. So is a
     * row for {@code InvariantChecker}, which is where the edge was.
     */
    private static final List<String> READING_ONE = List.of(
            "souther/compiler/check/AdmissibleReading",
            "souther/compiler/partition/Partitions");

    @Test
    void everyClassThatReadsOneIsWrittenDownWithWhatItReadsItFor() {
        assertEquals(READING_ONE, new ArrayList<>(readingOne()),
                "what a rule about a string means for a position is worked out once, by the reading"
                        + " that turns clauses into sets: a row that is not one of these is a reader"
                        + " deciding it a second time, and the two agree only until one of them"
                        + " changes");
    }

    /**
     * The walk reads every module's classes.
     *
     * <p>Asked of the modules the repository has and not of what a build happened to leave: a module
     * whose classes are missing is one whose reads this cannot see, and the rows from the rest would
     * match and this would pass while answering about fewer modules than it names.
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
        assertTrue(modulesRead() > 1,
                "the classes this reads are in more than the one module that declares the table");
    }

    /**
     * And the walk finds a reader that is there.
     *
     * <p>The rows above are what may read the table; this is that the reading which does read it is
     * one this walk can see. Matched on an owner nothing names, every row would be absent and the
     * list above would be empty and equal to itself.
     */
    @Test
    void andTheWalkSeesAReaderThatIsThere() {
        assertTrue(readingOne().contains("souther/compiler/check/AdmissibleReading"),
                "the reading that turns a predicate into the strings it admits reads the table, so a"
                        + " walk that cannot find it is finding nothing at all");
    }

    /** Every class whose constant pool names a member of the table, or of one of its answers. */
    private static Set<String> readingOne() {
        Set<String> found = new TreeSet<>();
        for (Path module : REPOSITORY.modules()) {
            for (Path each : classesUnder(module)) {
                String reader = internalName(module, each);
                // The table and the answers it declares are the table. What each of them names of
                // the others is the reading being written down and taken apart where it is made,
                // and a row for one of them would be this walk reporting the owner as a reader of
                // itself.
                if (names(reader)) {
                    continue;
                }
                for (PoolEntry entry : constantPoolOf(each)) {
                    if (entry instanceof MemberRefEntry member
                            && names(member.owner().name().stringValue())) {
                        found.add(reader);
                    }
                }
            }
        }
        return found;
    }

    /** Whether a member's owner is the table or one of the answers it declares. */
    private static boolean names(String owner) {
        return owner.equals(OWNER) || owner.startsWith(OWNER + "$");
    }

    private static int modulesRead() {
        int read = 0;
        for (Path module : REPOSITORY.modules()) {
            if (!classesUnder(module).isEmpty()) {
                read++;
            }
        }
        return read;
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
