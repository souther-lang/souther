package souther.bench;

import org.junit.jupiter.api.Test;

import souther.bench.PositionReadings.Authority;
import souther.bench.PositionReadings.Traversal;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the walk over a stage's readings sees, asked of code written to be read.
 *
 * <p>The rule beside this one says the compiler has no path from its partitioning stage to raw
 * structure. That is a fact about the compiler as it stands, and it stays green if the walk stops
 * seeing something: break the collection of one instruction and, with no such path written today,
 * nothing goes red. What the rule protects would be gone and nothing would say so.
 *
 * <p>So the walk is asked here about a model that holds one of everything. Each fixture is a claim
 * a reader can check by reading it — this reaches a declaration, this takes a compound apart, this
 * one only reads a name — and the walk's answer is held against it. A mutation run once against
 * the compiler proves the walk saw a defect that day; this says it still would.
 *
 * <p>The model is written in sums of its own. What the walk is handed is which sum says what a
 * module wrote and which is built out of others, so a model with its own asks whether those sets
 * are derived from the classes it was given rather than known. Written in the compiler's types, a
 * fixture would be checking a spelling.
 */
class ThisReadingSeesAReadingOfRawStructureTest {

    /** The stage of the model, whose readers are the ones held to the rule. */
    private static final String STAGE = "souther.bench.readings.Stage";

    private static final List<Authority> AUTHORITIES = List.of(
            new Authority("how a name is written where a reader meets one",
                    "souther.bench.readings.Opaque", Traversal.OPAQUE),
            new Authority("what a name comes to on the way",
                    "souther.bench.readings.Transparent", Traversal.TRANSPARENT));

    private static PositionReadings.Over model() throws IOException {
        return new PositionReadings.Over(written(), STAGE,
                "souther.bench.readings.Written$Declared", "souther.bench.readings.Written$Names#declaredNode",
                "souther.bench.readings.Written$Position$Built",
                "Lsouther/bench/readings/Written$Position;", AUTHORITIES);
    }

    /**
     * The compiled model, which is what this is a reading of.
     *
     * <p>Found from the repository, the way everything else here finds what a build produced. Read
     * from wherever this happens to have been started instead, the model would be missing whenever
     * that was somewhere else — and a walk over no classes finds no reading and says nothing.
     */
    private static List<Path> written() throws IOException {
        Path built = Reactor.root().resolve("souther-bench/target/test-classes/souther/bench/readings");
        assertTrue(Files.isDirectory(built),
                "the model was not compiled, so this would assert nothing: " + built);
        try (Stream<Path> walk = Files.walk(built)) {
            List<Path> out = new ArrayList<>(
                    walk.filter(each -> each.toString().endsWith(".class")).toList());
            assertFalse(out.isEmpty(), "the model compiled to no classes");
            return out;
        }
    }

    private static List<String> bypassing() throws IOException {
        return PositionReadings.of(model()).named();
    }

    /**
     * Every reader that reaches raw structure is seen, and only those.
     *
     * <p>Both halves at once, and named rather than counted. A walk that saw one shape and not
     * another would pass a check that only asked how many there were, and which shapes it sees is
     * the whole of what this is about.
     */
    @Test
    void everyReaderThatReachesRawStructureIsSeenAndNoOtherIs() throws IOException {
        assertEquals(List.of(
                        // Its own code reaches a declaration, and its own code takes a compound
                        // apart. The two plainest readings there are.
                        // Asking which compound a position is and taking nothing out of it, which
                        // is the reading a walk over components alone would not see.
                        "asksWhichCompoundItIs",
                        "readsADeclaration",
                        // Past an owner the walk is told to go through, which is what keeps a
                        // caller's own reading from hiding behind one.
                        "readsPastATransparentBoundary",
                        // Two calls away, behind something that answers with a word. What is
                        // followed is the call: a walk over what came back would see neither.
                        "readsThroughAHelper",
                        "takesACompoundApart",
                        "takesOneApartThroughAHelper"),
                bypassing(),
                "the readers the walk sees, against the ones written to be seen. A reader missing"
                        + " from this is a shape the walk has stopped seeing, and one that is here"
                        + " and should not be reads no structure at all");
    }

    /**
     * What the walk does not call a reading, said as itself.
     *
     * <p>The same list read the other way. These are the four ways of touching the model that are
     * not readings of it, and a walk calling any of them one would refuse code that is doing
     * nothing wrong — which is how a rule stops being read.
     */
    @Test
    void touchingTheModelWithoutReadingItIsNotOne() throws IOException {
        List<String> seen = bypassing();
        for (String each : List.of("asksAnAuthority", "readsANameOffALeaf", "makesACompound",
                "readsAComponentHoldingNoPosition")) {
            assertFalse(seen.contains(each), () -> each + " reads no structure, and the walk says"
                    + " it does. What it does instead is written on it: " + seen);
        }
    }

    /** An authority the stage arrives at is not reported as a boundary that is not there. */
    @Test
    void anAuthorityTheStageArrivesAtIsNotStale() throws IOException {
        PositionReadings.Over over = model();
        assertEquals(List.of(), PositionReadings.unreached(over, PositionReadings.of(over)),
                "both authorities are called by the stage of the model");
    }

    /**
     * And one nothing arrives at is, which is what a boundary that has gone looks like.
     *
     * <p>Named as a method of an authority that is there, because that is the way an entry goes
     * stale: the place stays and the operation the table pointed at is renamed or removed under it.
     */
    @Test
    void anAuthorityNothingArrivesAtIsStale() throws IOException {
        PositionReadings.Over over = model();
        List<Authority> withOneMore = new ArrayList<>(AUTHORITIES);
        withOneMore.add(new Authority("a question nothing in the model asks any more",
                "souther.bench.readings.Opaque#spellingAsItWasCalled", Traversal.OPAQUE));
        PositionReadings.Over stale = new PositionReadings.Over(over.classes(), over.stage(),
                over.declaration(), over.lookup(), over.compound(), over.held(), withOneMore);

        assertEquals(List.of("souther.bench.readings.Opaque#spellingAsItWasCalled"),
                PositionReadings.unreached(stale, PositionReadings.of(stale)),
                "nothing of that name is there to be called, so naming it is a rule about a"
                        + " boundary that is not");
    }

    /**
     * An opaque boundary stops the walk, and what it reads to answer is its own business.
     *
     * <p>Asked by taking the boundary away: the reader that asks it is not a bypass while the
     * authority is named and is one when it is not. Without this the table could hold entries that
     * change nothing, and an authority that stopped stopping anything would look like a clean
     * compiler.
     */
    @Test
    void anOpaqueBoundaryIsWhatStopsTheWalk() throws IOException {
        assertFalse(bypassing().contains("asksAnAuthority"),
                "the authority answers, so its caller reaches nothing raw");

        PositionReadings.Over over = model();
        PositionReadings.Over without = new PositionReadings.Over(over.classes(), over.stage(),
                over.declaration(), over.lookup(), over.compound(), over.held(),
                AUTHORITIES.stream()
                        .filter(each -> each.traversal() != Traversal.OPAQUE).toList());
        List<String> reaching = PositionReadings.of(without).named();
        assertTrue(reaching.contains("asksAnAuthority"),
                "with nothing answering for it, the same reader reaches the declaration behind it:"
                        + " " + reaching);
    }
}
