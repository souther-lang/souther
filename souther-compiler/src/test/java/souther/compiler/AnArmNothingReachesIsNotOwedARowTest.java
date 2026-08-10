package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.types.CoverageOrigin;

import souther.compiler.coverage.CoverageSites;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.partition.GuardEdge;
import souther.compiler.partition.GuardReachability;
import souther.compiler.partition.NumericTerm;
import souther.compiler.partition.TermPath;
import souther.compiler.query.Adequacy;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.math.BigDecimal;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An arm the model's own rules prove nothing reaches is not a row anybody is owed.
 *
 * <p>The cap on {@code b} is written on the record, so {@code Count} alone says nothing about it and a
 * guard at 50 sits outside what any pair can hold. What a position is divided into and which lines are
 * owed a row already knew that; the arms did not, and a report asking for a row through an arm nothing
 * can reach is asking for work nobody can do.
 *
 * <p>Instrumented is not the same as owed. The probe on that arm stays, because a probe is the only
 * thing that could show the reachability wrong.
 */
class AnArmNothingReachesIsNotOwedARowTest {

    private static final String CAPPED = """
            module example.capped

            data Count = Int
                invariant lower = value >= 0

            data Pair =
                { a: Count
                , b: Count
                }
                invariant cap = b <= 10
                invariant ordered = a < b

            data Small
            data Big

            behavior classify : (pair: Pair) -> Small | Big
                constructs Small, Big

            let classify (pair) =
                if pair.b.value >= 50
                    then Big
                    else Small

            example classify
                | "small" : (Pair { a = Count(0), b = Count(1) }) -> Small
            """;

    private static String reportOn(String model) throws Exception {
        Path file = Files.createTempDirectory("souther-arms").resolve("model.sou");
        Files.writeString(file, model);
        PrintStream was = System.out;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            Main.main(new String[] {"examples", file.toString()});
        } finally {
            System.setOut(was);
        }
        return out.toString(StandardCharsets.UTF_8);
    }

    @Test
    void anArmBeyondTheRecordsCapIsNotCounted() throws Exception {
        String report = reportOn(CAPPED);

        assertTrue(report.contains("branch      1/1"),
                () -> "the `else` arm is the only one a pair can take:\n" + report);
        assertFalse(report.contains("no row goes through"),
                () -> "and it was taken:\n" + report);
    }

    /** The same guard one value lower, which a pair can hold. Without this the assertion above would
     * pass on a measure that had stopped counting arms at all. */
    @Test
    void anArmWithinItStillIs() throws Exception {
        String report = reportOn(CAPPED.replace("pair.b.value >= 50", "pair.b.value >= 5"));

        assertTrue(report.contains("branch      1/2"),
                () -> "a `b` of 5 is a value some pair holds, so both arms are owed:\n" + report);
        assertTrue(report.contains("no row goes through `then`"),
                () -> "and no row went through this one:\n" + report);
    }

    // --- the cases behind such an arm -------------------------------------------------------------

    @Test
    void aCaseOnlyThatArmProducesIsNotOwedEither() throws Exception {
        String report = reportOn(CAPPED);

        assertTrue(report.contains("out specified 1/1"),
                () -> "`Big` is answered only where nothing reaches:\n" + report);
        assertFalse(report.contains("no row expects `Big`"), () -> report);
        assertTrue(report.contains("adequacy: satisfied"),
                () -> "and everything left is covered:\n" + report);
    }

    /** The same case built somewhere a row can get to. One producer proving nothing about the others
     * is the whole reason this is a union over producers rather than a fact about the case. */
    @Test
    void aCaseAReachableArmAlsoProducesStaysOwed() throws Exception {
        String report = reportOn(CAPPED.replace("        else Small",
                "        else if pair.a.value >= 1 then Big else Small"));

        assertTrue(report.contains("no row expects `Big`"),
                () -> "an `a` of 1 is a value some pair holds:\n" + report);
    }

    /**
     * A producer this cannot read keeps every case owed.
     *
     * <p>The body answers with a name rather than with a value built in a tail position, and what that
     * name holds is not followed. That is the top of the analysis, and it is where anything unreadable
     * goes: taking a case away on a guess is how an author stops being asked for a row they could have
     * written.
     */
    @Test
    void aCaseWhoseProducerCannotBeReadStaysOwed() throws Exception {
        String report = reportOn(CAPPED.replace("""
                let classify (pair) =
                    if pair.b.value >= 50
                        then Big
                        else Small
                """, """
                let classify (pair) = {
                    let answer = if pair.b.value >= 50 then Big else Small
                    answer
                }
                """));

        assertTrue(report.contains("no row expects `Big`"),
                () -> "nothing here says what `answer` holds:\n" + report);
    }

    /**
     * A case nothing answers with is not the same as a case nothing can answer with.
     *
     * <p>What is taken away here is a case something does answer with, at a place the rules prove
     * nothing reaches. A case the body has no producer for stays: that a signature says {@code A | B}
     * and the implementation never answers `B` is a gap between the two, and it is the kind of gap
     * this measure is for.
     */
    @Test
    void onlyACaseSomethingAnswersWithBehindAProvenArmIsTakenAway() throws Exception {
        String model = """
                module example.threeways

                data N = Int
                    invariant cap = value <= 10

                data A
                data B

                behavior f : (n: N) -> A | B
                    constructs BUILDS

                let f (n) = BODY

                example f
                    | "one" : (N(1)) -> A
                """;
        String dead = reportOn(model.replace("BODY", "if n.value > 100 then B else A")
                .replace("BUILDS", "A, B"));
        String none = reportOn(model.replace("BODY", "A").replace("BUILDS", "A"));
        String live = reportOn(model.replace("BODY", "if n.value > 5 then B else A")
                .replace("BUILDS", "A, B"));

        assertTrue(dead.contains("out specified 1/1"),
                () -> "`B` is answered only where nothing reaches:\n" + dead);
        assertTrue(none.contains("out specified 1/2"),
                () -> "nothing answers `B` here, which is a gap and not an impossibility:\n" + none);
        assertTrue(live.contains("out specified 1/2"),
                () -> "and here a row can take the arm that answers it:\n" + live);
    }

    /**
     * The cases left are named in the order they were declared in.
     *
     * <p>A report is read against the declaration it came from, so the list has to run the way that
     * declaration does. Taking a case out of the middle is where the order is easiest to lose: what
     * is left is a new set, and a set that keeps the values is not one that keeps their order.
     */
    @Test
    void whatIsLeftKeepsTheOrderItWasDeclaredIn() throws Exception {
        String report = reportOn("""
                module example.order

                data N = Int
                    invariant cap = value <= 10

                data Alpha
                data Beta
                data Gamma
                data Delta
                data Epsilon
                data Zeta
                data Kind = Alpha | Beta | Gamma | Delta | Epsilon | Zeta

                behavior f : (n: N) -> Kind
                    constructs Alpha, Beta

                let f (n) =
                    if n.value > 100 then Beta else Alpha

                example f
                    | "one" : (N(1)) -> Alpha
                """);

        assertTrue(report.contains("out specified 1/5"),
                () -> "`Beta` is answered only where nothing reaches:\n" + report);
        List<String> named = report.lines().map(String::trim)
                .filter(line -> line.startsWith("· no row expects"))
                .map(line -> line.substring(line.indexOf('`') + 1, line.lastIndexOf('`')))
                .toList();
        assertEquals(List.of("Gamma", "Delta", "Epsilon", "Zeta"), named,
                () -> "the order `Kind` lists them in:\n" + report);
    }

    // --- what happens if the proof is wrong -------------------------------------------------------

    private static CoverageSites.Site arm(int index) {
        return new CoverageSites.Site("classify", CoverageSites.Site.Kind.THEN, "then", null,
                index, index,
                new CoverageSites.Obligation("classify", CoverageOrigin.written("t", index), 0));
    }

    /** A reachability that proves arm 0 unreachable: nothing at or above 50 is a value of [0, 10]. */
    private static GuardReachability proving() {
        GuardEdge edge = GuardEdge.above(
                new CoverageSites.GuardRef("classify", CoverageOrigin.written("t", 0), 0, 1, null),
                0, new NumericTerm.ValueOf(TermPath.of("pair")), BigDecimal.valueOf(50), true);
        return GuardReachability.of(List.of(edge),
                Map.of(new NumericTerm.ValueOf(TermPath.of("pair")),
                        new NumericDomain.Bounds(Endpoint.inclusive(BigDecimal.ZERO),
                                Endpoint.inclusive(BigDecimal.TEN))));
    }

    @Test
    void aProvenArmLeavesTheDenominator() {
        Adequacy.BranchEvidence measured = Adequacy.BranchEvidence.measured(
                List.of(arm(0), arm(1)), Set.of(1),
                new Adequacy.Effective(proving(), Set.of()), MeasurementStatus.COMPLETE);

        assertEquals(List.of(1), measured.all().stream().map(CoverageSites.Site::index).toList());
        assertEquals(Set.of(1), measured.covered());
        assertTrue(measured.contradicted().isEmpty());
        assertTrue(measured.unreached().isEmpty());
    }

    /**
     * A row through an arm nothing was supposed to reach.
     *
     * <p>Then the model is fine and the proof is not. The arm is back in the denominator before this
     * measure sees it, and what is left to do here is to refuse to report a complete measurement over
     * a proof already known to be wrong.
     */
    @Test
    void anArmObservedAgainstTheProofIsKeptAndSaidSo() {
        GuardReachability proven = proving();
        Adequacy.Effective effective = new Adequacy.Effective(
                proven.without(Set.of(0)), Set.of(0));
        Adequacy.BranchEvidence measured = Adequacy.BranchEvidence.measured(
                List.of(arm(0), arm(1)), Set.of(0, 1), effective, MeasurementStatus.COMPLETE);

        assertEquals(Set.of(0), measured.contradicted(),
                "arm 0 was proven unreachable and a row went through it");
        assertEquals(List.of(0, 1),
                measured.all().stream().map(CoverageSites.Site::index).toList(),
                "so it is still an arm this behavior has");
        assertEquals(Set.of(0, 1), measured.covered());
        assertEquals(MeasurementStatus.PARTIAL, measured.status(),
                "and no number here is given as though nothing had happened");
    }

    /** The same fact both measures read. Taking the arm back for one of them and not the other is how
     * the case behind it would stay unowed over a proof already disproved. */
    @Test
    void theSameArmIsBackForEveryMeasure() {
        Adequacy.Effective effective = new Adequacy.Effective(
                proving().without(Set.of(0)), Set.of(0));

        assertFalse(effective.reachable().provenUnreachable(0),
                "a row went through it, so nothing about it is proven any more");
        assertTrue(effective.reachable().isEmpty(),
                "and what the signature reads is the same set the arms are counted by");
    }
}
