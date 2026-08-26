package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.test.RepositoryLayout;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The readings that discharge an invariant ask what a position is; they do not work it out.
 *
 * <p>What kind of thing stands at a position is {@link Shape}'s answer and what the model writes
 * there is {@link PositionReading}'s. A reader that resolves a name to a declaration and switches on
 * what it finds has a second way to answer both, and two answers about one position is how a field
 * every case of a sum spreads came to be readable off the sum by the elaborator and invisible to the
 * check that reads what the sum guarantees.
 *
 * <p><b>Narrow on purpose.</b> Not every {@code instanceof Hir.Data} in the compiler is this
 * mistake — enumerating the declarations that write an invariant is a different question, and so is
 * resolving what a construction builds — and a check that refused all of them would need an
 * exception list longer than the rule. What is held here is the set of files that read a position on
 * the way to discharging an invariant, and they resolve no declaration at all.
 *
 * <p>A tripwire and not a proof. A helper in between defeats it; what it does see is the line that
 * has to be written first.
 */
class TheInvariantReadingAsksWhatAPositionIsRatherThanDecidingTest {

    /** Read once: what this asks of it does not change between its checks. */
    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    /** The files that read a position on the way to discharging an invariant. */
    private static final List<String> THE_READING = List.of(
            "TypeGuarantees.java",
            "GuaranteeWalk.java",
            "PathEngine.java",
            "UniversalElementFacts.java",
            "StepInputFacts.java");

    /**
     * None of them resolves a name to a declaration.
     *
     * <p>Of the code and not of the prose, so that explaining the rule in a javadoc and breaking it
     * are not the same thing to this check.
     */
    @Test
    void theReadingResolvesNoDeclarationOfItsOwn() throws IOException {
        List<String> resolving = new ArrayList<>();
        for (Path source : theReading()) {
            String code = code(source);
            if (code.contains("declarations().declaration(")
                    || code.contains("instanceof Hir.SumData")
                    || code.contains("instanceof Hir.UnitData")) {
                resolving.add(source.getFileName().toString());
            }
        }

        assertEquals(List.of(), resolving,
                "these decide what a position is instead of asking; what stands at one is"
                        + " PositionReading's answer");
    }

    /**
     * And what a sum's cases share is worked out in one place.
     *
     * <p>Of who makes one and not of who reads one. Reading {@code Shape.Sum.common} is what a
     * consumer of the shape is supposed to do — the elaborator and the construction checker both
     * do, and so does the backend — and the answer being one answer rests on nobody else deriving
     * it from the declarations.
     */
    @Test
    void whatASumsCasesShareIsDerivedInOnePlace() throws IOException {
        List<String> deriving = new ArrayList<>();
        for (Path source : REPOSITORY.mainJavaSources()) {
            if (code(source).contains("new Shape.CommonProduct.Shared(")) {
                deriving.add(source.getFileName().toString());
            }
        }

        assertEquals(List.of("TypeOps.java"), deriving,
                "the shared part of a sum is derived where the spreads are intersected, and read"
                        + " off the shape everywhere else");
    }

    private static List<Path> theReading() throws IOException {
        List<Path> found = new ArrayList<>();
        for (Path source : REPOSITORY.mainJavaSources()) {
            if (THE_READING.contains(source.getFileName().toString())) {
                found.add(source);
            }
        }
        assertEquals(THE_READING.size(), found.size(),
                "a file this holds was renamed or moved, and the check stopped seeing it: " + found);
        return found;
    }

    private static String code(Path source) throws IOException {
        return withoutComments(Files.readString(source, StandardCharsets.UTF_8));
    }

    /**
     * The source with its comments taken out.
     *
     * <p>Lexical and small, and deliberately not a parser. It follows string and character literals
     * so that a {@code //} inside one does not read as a comment, and it keeps what is inside them —
     * so the worst it can do is leave a comment standing, never take code away.
     */
    private static String withoutComments(String source) {
        StringBuilder out = new StringBuilder(source.length());
        int at = 0;
        while (at < source.length()) {
            char here = source.charAt(at);
            char next = at + 1 < source.length() ? source.charAt(at + 1) : '\0';
            if (here == '/' && next == '/') {
                while (at < source.length() && source.charAt(at) != '\n') {
                    at++;
                }
            } else if (here == '/' && next == '*') {
                at += 2;
                while (at + 1 < source.length()
                        && !(source.charAt(at) == '*' && source.charAt(at + 1) == '/')) {
                    at++;
                }
                at = Math.min(source.length(), at + 2);
            } else if (here == '"' || here == '\'') {
                out.append(here);
                at++;
                while (at < source.length() && source.charAt(at) != here) {
                    if (source.charAt(at) == '\\' && at + 1 < source.length()) {
                        out.append(source.charAt(at));
                        at++;
                    }
                    out.append(source.charAt(at));
                    at++;
                }
                if (at < source.length()) {
                    out.append(source.charAt(at));
                    at++;
                }
            } else {
                out.append(here);
                at++;
            }
        }
        return out.toString();
    }
}
