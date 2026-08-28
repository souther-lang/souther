package souther.compiler.execute.jvm;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An arrangement is handed the term and does not go looking for it.
 *
 * <p>What a run is held to is the compile's and reaches the machine as an argument:
 * {@link JvmExampleDeadlines#forThisCompile} takes the wait. An arrangement that reached back into
 * the compilation for it instead would have two ways to learn one thing, and that is not a
 * hypothetical — the wait was read out of the store beside a deadline set there, so the boundary
 * stated a minute while the run was being given up on after five milliseconds.
 *
 * <p>The other half of {@code NoInputOfACompilationIsOneMachinesArrangementTest}, and the half a
 * walk over types cannot answer. That one reads what an input carries, which catches an input whose
 * value is the machine's. It cannot catch {@code Input<Long>} holding a number of bytes of a
 * thread's stack, because nothing about {@code Long} says so — and that is the one that was there.
 * This asks the question from the end where the type is not the evidence: whatever the key is
 * called, an arrangement may not come to the store to read it.
 *
 * <p>Read from the source rather than the bytecode, so that a name reached through a helper counts
 * the same as one reached directly. What an arrangement needs is what it was handed and what it was
 * built with; a reader of the compilation's store is neither.
 */
class TheArrangementThatKeepsATermDoesNotAskTheCompilationForItTest {

    /** How this compiler holds and answers its own questions. */
    private static final List<String> THE_STORE = List.of("Front", "Db", "Output", "Key<");

    private static final Path MAIN = Path.of("src/main/java");

    /**
     * No arrangement names the store.
     */
    @Test
    void nothingThatKeepsATermReadsTheCompilationsAnswers() throws IOException {
        List<String> naming = new ArrayList<>();
        for (Path each : arrangements()) {
            String written = Files.readString(each);
            for (String store : THE_STORE) {
                if (written.contains(store)) {
                    naming.add(each.getFileName() + " names " + store);
                }
            }
        }

        assertEquals(List.of(), naming,
                "an arrangement keeps the term it is handed; reading one out of the store is the"
                        + " second answer that JvmExampleDeadlines exists to do without");
    }

    /** And the arrangements this reads are the ones there are. */
    @Test
    void andEveryArrangementThereIsWasRead() throws IOException {
        assertEquals(Set.of("JvmDeadlines.java", "ChosenJvmExampleDeadlines.java",
                        "CallerCrossingDeadlines.java"),
                arrangements().stream().map(p -> p.getFileName().toString())
                        .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new)),
                "a new way of running this compile's rows is read by this too; adding one means"
                        + " saying so here");
    }

    /**
     * Every file that says how a deadline is kept: one that answers {@link JvmExampleDeadlines},
     * and one that is a {@code Deadline}.
     *
     * <p>Both spellings of the second, because which one a file uses says nothing about whether it
     * reads the store. {@code Deadline} is not sealed — a class may answer it as readily as an
     * anonymous body does — so looking only for the body that is here today would let the next one
     * past.
     */
    private static List<Path> arrangements() throws IOException {
        List<Path> found = new ArrayList<>();
        try (Stream<Path> written = Files.walk(MAIN)) {
            for (Path each : written.filter(p -> p.toString().endsWith(".java")).sorted().toList()) {
                String said = Files.readString(each);
                if (said.contains("implements JvmExampleDeadlines")
                        || said.contains("implements Deadline")
                        || said.contains("new Deadline() {")) {
                    found.add(each);
                }
            }
        }
        return found;
    }
}
