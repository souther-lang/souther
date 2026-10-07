package souther.compiler;

import souther.compiler.diag.Located;
import souther.compiler.diag.SourceRendering;
import souther.compiler.meta.ModulePath;
import souther.compiler.partition.BodyDistinction;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.ReaderDisposition;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A position holding more classes than the behavior's body tells apart says both, and what a reader
 * is left with there is a decision.
 *
 * <p>The cases of a sum are classes of the position whether or not the body looks at them. So a
 * behavior may take five cases and decide one two-way question with them: every measure over the
 * position comes back full, and the combinations those classes take part in stay unknown, because
 * no row can reach a combination the model has and the behavior never tells apart. A reader handed
 * that count and nothing else reads it as work owed and writes a row that buys a combination and no
 * evidence.
 *
 * <p>What the body tells apart at a position, shape by shape, is held by the fixtures
 * ({@code EachFixtureIsToldApartAsItSaysTest}). What is here is what is made of it: the sentence a
 * report writes, which positions make combinations, and where a reader is sent.
 *
 * <p>Neither is a finding and no row answers either. Whether to narrow the input, split the
 * behavior, or leave it as a value this one passes through is the author's, and this compiler knows
 * none of it: what it can say is what it worked out.
 */
class APositionSaysHowFarTheBodyTellsItsClassesApartTest {

    /** Five cases the body never asks about: the line says the body tells none of them apart. */
    @Test
    void aPositionTheBodyTellsNothingApartIsSaidToBe() {
        String human = report("""
                module example.untouched

                data TooShort
                data TooLong
                data WrongCase
                data Repeated
                data Banned
                data Refusal = TooShort | TooLong | WrongCase | Repeated | Banned

                data Ok = { n: Int }

                behavior judge : (why: Refusal, n: Int) -> Ok
                    constructs Ok

                let judge (why, n) = {
                    guard n > 10 else Ok { n = 0 }
                    Ok { n = 1 }
                }

                example judge
                    | (TooShort, 5)  -> Ok { n = 0 }
                    | (TooLong, 50)  -> Ok { n = 1 }
                """);

        assertTrue(human.contains("why holds 5 classes and this behavior does not tell them apart"),
                () -> "the cases are classes and the body looks at none of them: " + human);
    }

    /** Four cases told apart as two groups: the line says how many groups. */
    @Test
    void aPositionToldApartInPartIsSaidToBeAsManyGroups() {
        String human = report("""
                module example.grouped

                data K1
                data K2
                data K3
                data K4
                data Kind = K1 | K2 | K3 | K4

                data Ok = { n: Int }

                behavior judge : (k: Kind, n: Int) -> Ok
                    constructs Ok

                let judge (k, n) = {
                    guard n > 10 else Ok { n = 0 }
                    match k with
                        | K1 | K2 -> Ok { n = 1 }
                        | K3 | K4 -> Ok { n = 2 }
                }

                example judge
                    | (K1, 5)  -> Ok { n = 0 }
                    | (K1, 50) -> Ok { n = 1 }
                    | (K3, 50) -> Ok { n = 2 }
                """);

        assertTrue(human.contains("k holds 4 classes and this behavior tells them apart as 2 groups"),
                () -> "two arms over four cases are two groups: " + human);
    }

    /**
     * A sum every case of which a {@code match} has an arm for says nothing, and leaves nothing
     * further.
     *
     * <p>The rows leave a combination unknown, so the line would be raised for any position the body
     * tells apart less than in full.
     */
    @Test
    void aPositionToldApartInFullSaysNothing() {
        String model = """
                module example.matched

                data Draft
                data Submitted
                data Request = Draft | Submitted

                data Ok = { n: Int }

                behavior judge : (r: Request, n: Int) -> Ok
                    constructs Ok

                let judge (r, n) = {
                    guard n > 10 else Ok { n = 0 }
                    match r with
                        | Draft -> Ok { n = 1 }
                        | Submitted -> Ok { n = 2 }
                }

                example judge
                    | (Draft, 5)      -> Ok { n = 0 }
                    | (Draft, 50)     -> Ok { n = 1 }
                    | (Submitted, 50) -> Ok { n = 2 }
                """;
        String human = report(model);
        PartitionEvidence partition = coverageOf(model, "example.matched");

        assertTrue(partition.pairs().space().stream().anyMatch(p -> partition.pairs().unknown(p) > 0),
                () -> "a combination the rows do not sit in: " + partition.pairs());
        assertFalse(human.contains(" classes and this behavior "),
                () -> "a match over every case tells every case apart: " + human);
        assertInstanceOf(ReaderDisposition.Settled.class,
                ReaderDisposition.of(partition.pairs(), partition.axes()),
                () -> "nothing is taken wider than the body tells apart: " + partition.axes());
    }

    /**
     * And a position what is told apart at is not read says nothing either.
     *
     * <p>Whether the construction held its rules tells {@code Off} from the other two, and which
     * values an attempt tells apart is nothing its arms name — so what the body tells apart at
     * {@code f} is read in part. A part is not said as the whole: no line, and nothing for a reader
     * to weigh.
     */
    @Test
    void aPositionWhatIsToldApartAtIsNotReadSaysNothing() {
        String model = """
                module example.bound

                data On
                data Off
                data Pending
                data Flag = On | Off | Pending
                data Active = Flag invariant value /= Off
                data NotActive
                data Ok = { n: Int }

                behavior judge : (f: Flag, n: Int) -> Ok | NotActive
                    constructs Ok, Active

                let judge (f, n) = {
                    guard n > 10 else Ok { n = 0 }
                    guard Active(f) as active else NotActive
                    match f with
                        | On | Pending -> Ok { n = 1 }
                        | Off -> Ok { n = 2 }
                }

                example judge
                    | (On, 5)  -> Ok { n = 0 }
                    | (On, 50) -> Ok { n = 1 }
                """;
        String human = report(model);
        PartitionEvidence partition = coverageOf(model, "example.bound");

        assertInstanceOf(BodyDistinction.Unread.class, partition.axes().stream()
                        .filter(each -> each.name().equals("f")).findFirst().orElseThrow()
                        .toldApart(),
                () -> "what the body tells apart is read in part: " + partition.axes());
        assertFalse(human.contains("f holds"),
                () -> "and nothing is said about what was read in part: " + human);
        assertInstanceOf(ReaderDisposition.Settled.class,
                ReaderDisposition.of(partition.pairs(), partition.axes()),
                () -> "nothing to weigh at a position not read: " + partition.axes());
    }

    /**
     * A position the body tells nothing apart about makes no combination to count.
     *
     * <p>A reader shown "some combinations are unknown" writes a row, moves the number by one and
     * buys no evidence with it — and the reason they buy none is that this behavior never tells the
     * position apart. So the space is over what the body says something about, and a position it
     * says nothing about is in none of it.
     */
    @Test
    void aPositionTheBodyTellsNothingApartMakesNoCombination() {
        String human = report("""
                module example.owed

                data TooShort
                data TooLong
                data WrongCase
                data Refusal = TooShort | TooLong | WrongCase

                data Ok = { n: Int }

                behavior judge : (why: Refusal, n: Int) -> Ok
                    constructs Ok

                let judge (why, n) = {
                    guard n > 10 else Ok { n = 0 }
                    Ok { n = 1 }
                }

                example judge
                    | (TooShort, 5)  -> Ok { n = 0 }
                    | (TooLong, 50)  -> Ok { n = 1 }
                """);

        assertFalse(human.contains("    combination "),
                () -> "a position this behavior separates none of is in no combination: " + human);
    }

    /**
     * Nor does one the body reads and sends every class of one way.
     *
     * <p>One arm for both cases is a decision about {@code k} that tells nothing apart, which is what
     * a position nothing in the body is about comes to as well.
     */
    @Test
    void aPositionTheBodySendsAllOneWayMakesNoCombination() {
        PartitionEvidence partition = coverageOf("""
                module example.oneway

                data A
                data B
                data Kind = A | B

                data Ok = { n: Int }

                behavior judge : (k: Kind, n: Int) -> Ok
                    constructs Ok

                let judge (k, n) = {
                    guard n > 10 else Ok { n = 0 }
                    match k with
                        | A | B -> Ok { n = 1 }
                }

                example judge
                    | (A, 50) -> Ok { n = 1 }
                """, "example.oneway");
        PartitionEvidence.AxisCoverage k = partition.axes().stream()
                .filter(each -> each.name().equals("k")).findFirst().orElseThrow();

        assertInstanceOf(BodyDistinction.Drawn.class, k.toldApart(), () -> "at " + k);
        assertTrue(partition.pairs().space().stream().noneMatch(pair ->
                        pair.between().one().equals(k.at()) || pair.between().other().equals(k.at())),
                () -> "no combination with `k`: " + partition.pairs());
    }

    /**
     * What a reader is left with at a position taken wider than it is told apart is a decision.
     *
     * <p>Not that they narrow anything — a value passed through untouched is as ordinary as an input
     * wider than it needs to be — and not a row, since nobody is owed one at a combination.
     */
    @Test
    void aBehaviorWiderThanItSeparatesLeavesADecisionAtThePosition() {
        PartitionEvidence partition = coverageOf("""
                module example.left

                data TooShort
                data TooLong
                data WrongCase
                data Refusal = TooShort | TooLong | WrongCase

                data Ok = { n: Int }

                behavior judge : (why: Refusal, n: Int) -> Ok
                    constructs Ok

                let judge (why, n) = {
                    guard n > 10 else Ok { n = 0 }
                    Ok { n = 1 }
                }

                example judge
                    | (TooShort, 5)  -> Ok { n = 0 }
                    | (TooLong, 50)  -> Ok { n = 1 }
                """, "example.left");

        assertInstanceOf(ReaderDisposition.ReconsiderWhatThisBehaviorNeedsToDistinguish.class,
                ReaderDisposition.of(partition.pairs(), partition.axes()),
                () -> "a position it takes wider than it separates: " + partition.pairs());
    }

    /**
     * And where the body tells every position apart in full, nothing further.
     *
     * <p>Without this the arm above would be one this report reaches for whenever a combination is
     * unknown, which is most models: what the rows happen not to sit in is not the same as what
     * they cannot reach.
     */
    @Test
    void combinationsTheRowsMerelyMissLeaveNothingFurther() {
        PartitionEvidence partition = coverageOf("""
                module example.missed

                data Ok = { n: Int }

                behavior judge : (a: Int, b: Int) -> Ok
                    constructs Ok

                let judge (a, b) = {
                    guard a > 10 else Ok { n = 0 }
                    guard b > 10 else Ok { n = 1 }
                    Ok { n = 2 }
                }

                example judge
                    | (5, 5)   -> Ok { n = 0 }
                    | (50, 50) -> Ok { n = 2 }
                """, "example.missed");

        assertInstanceOf(ReaderDisposition.Settled.class,
                ReaderDisposition.of(partition.pairs(), partition.axes()),
                () -> "every position is told apart by the body's own comparisons: "
                        + partition.pairs());
    }

    /**
     * And a position whose own relations the rows all reach is not raised by another's.
     *
     * <p>Three positions, each told apart as two groups of three cases, and what is unknown is
     * between two of them. What makes a position worth a reader's time is that some of what it
     * carries is out of every row's reach, and that is a fact about a relation. Read off the space, a
     * position covered throughout would be raised because two others left something unknown.
     */
    @Test
    void aPositionWhoseOwnRelationsAreCoveredIsNotRaisedByAnothers() {
        PartitionEvidence partition = coverageOf("""
                module example.three

                data A1
                data A2
                data A3
                data As = A1 | A2 | A3

                data B1
                data B2
                data B3
                data Bs = B1 | B2 | B3

                data C1
                data C2
                data C3
                data Cs = C1 | C2 | C3

                data Ok = { n: Int }

                behavior judge : (a: As, b: Bs, c: Cs) -> Ok
                    constructs Ok

                let judge (a, b, c) =
                    Ok { n = (match a with | A1 -> 1 | A2 | A3 -> 0)
                            + (match b with | B1 -> 2 | B2 | B3 -> 0)
                            + (match c with | C1 -> 4 | C2 | C3 -> 0) }

                example judge
                    | (A1, B1, C1) -> Ok { n = 7 }
                    | (A1, B2, C2) -> Ok { n = 1 }
                    | (A1, B3, C3) -> Ok { n = 1 }
                    | (A2, B1, C1) -> Ok { n = 6 }
                    | (A2, B2, C2) -> Ok { n = 0 }
                    | (A2, B3, C3) -> Ok { n = 0 }
                    | (A3, B1, C1) -> Ok { n = 6 }
                    | (A3, B2, C2) -> Ok { n = 0 }
                    | (A3, B3, C3) -> Ok { n = 0 }
                """, "example.three");
        List<String> raised = ReaderDisposition
                .widerThanTheyAreSeparated(partition.pairs(), partition.axes()).stream()
                .map(each -> each.axis().at().term()).toList();

        // Every relation `a` is in was reached, and `b` and `c` leave one between them unknown.
        assertFalse(raised.contains("a"),
                () -> "every relation `a` takes part in is covered, so it is not raised: "
                        + raised + " over " + partition.pairs());
        assertTrue(raised.contains("b") && raised.contains("c"),
                () -> "the two that leave a relation unknown are raised: " + raised
                        + " over " + partition.pairs());
    }

    /**
     * A behavior with no body is not said to take a position wider than it tells apart.
     *
     * <p>What it tells apart is not known, and every combination is one a row can be written at and
     * one the rows happen not to sit in.
     */
    @Test
    void aBehaviorWithNoBodyLeavesNothingFurther() {
        PartitionEvidence partition = coverageOf("""
                module example.injected

                data Yes
                data No
                data Flag = Yes | No

                data A1
                data A2
                data A3
                data Wide = A1 | A2 | A3

                data Ok = { n: Int }

                behavior judge : (a: Flag, c: Wide) -> Ok

                example judge
                    | (Yes, A1) -> Ok { n = 0 }
                    | (No, A2)  -> Ok { n = 0 }
                """, "example.injected");

        assertTrue(partition.pairs().space().stream().anyMatch(p -> partition.pairs().unknown(p) > 0),
                () -> "a combination the rows do not sit in: " + partition.pairs());
        assertInstanceOf(ReaderDisposition.Settled.class,
                ReaderDisposition.of(partition.pairs(), partition.axes()),
                () -> "a behavior with no body is not taken wider than it tells apart: "
                        + partition.axes());
    }

    private static PartitionEvidence coverageOf(String model, String module) {
        return compiled(model).db().ask(new Adequacy.Coverage(module)).value().get("judge");
    }

    private static Compilation compiled(String model) {
        return Compiler.analyzedModules(List.of(model), ModulePath.EMPTY, new ArrayList<>(),
                Adequacy.Asked.fullReport());
    }

    private static String report(String model) {
        List<Located> warnings = new ArrayList<>();
        Compilation compilation = Compiler.analyzedModules(List.of(model), ModulePath.EMPTY,
                warnings, Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation).human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
