package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.claims.Claim;
import souther.compiler.claims.Claims;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.BoundaryTarget;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.GeneratedRows;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an attempted construction built is read, inside its {@code then}, through the name it binds.
 *
 * <p>{@code if Q(x) as q then ...} and {@code guard Q(x) as q else ...} bind {@code q} to what was
 * built, so {@code q.value} is the value handed to the field, which is the input position {@code x}.
 * Every reading that asks which position a name is has to know that, or the same model written
 * through an attempt measures less than it does written without one. Each model here is read by a
 * different one of those readings, and each is held to what the same rule says where no attempt
 * stands between it and the position.
 */
class WhatAnAttemptBuiltIsReadThroughItsNameTest {

    private static final String THRESHOLD = """
            module demo
            data Q = Int
                invariant value >= 0
            data Nope
            data Big
            data Small
            behavior size : (x: Int) -> Big | Small | Nope
                constructs Q
            let size (x) = if Q(x) as q then (if q.value > 10 then Big else Small) else Nope
            """;

    private static final String THRESHOLD_UNDER_A_GUARD = """
            module demo
            data Q = Int
                invariant value >= 0
            data Nope
            data Big
            data Small
            behavior size : (x: Int) -> Big | Small | Nope
                constructs Q
            let size (x) = {
                guard Q(x) as q else Nope
                if q.value > 10 then Big else Small
            }
            """;

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static PartitionEvidence evidence(String source, String behavior) {
        Compilation compilation = measured(source);
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        return all.get(behavior);
    }

    private static PartitionEvidence.AxisCoverage axis(PartitionEvidence evidence, String path) {
        return evidence.axes().stream().filter(each -> each.path().equals(path)).findFirst()
                .orElseThrow(() -> new AssertionError("no axis at " + path + ": "
                        + evidence.axes().stream().map(PartitionEvidence.AxisCoverage::path)
                        .toList()));
    }

    /**
     * The comparison written over what was built draws its line at the position it was built
     * from, whether the attempt is an {@code if} or a {@code guard}.
     */
    @Test
    void aComparisonOverWhatWasBuiltDrawsItsLineAtThePositionItWasBuiltFrom() {
        for (String source : List.of(THRESHOLD, THRESHOLD_UNDER_A_GUARD)) {
            PartitionEvidence size = evidence(source, "size");

            assertEquals(List.of("x/x <= 10", "x/10 < x"), axis(size, "x").classes(), source);
            assertEquals(List.of(), size.notRead(), () -> "the comparison is a line: " + source);
        }
    }

    /** And rows are offered on both sides of it. */
    @Test
    void rowsAreOfferedOnBothSidesOfTheLine() {
        Compilation compilation = measured(THRESHOLD);
        String block = GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("demo")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();

        assertTrue(block.contains("x <= 10") && block.contains("(10)"), block);
        assertTrue(block.contains("10 < x") && block.contains("(11)"), block);
    }

    /** A predicate written over what was built divides the position it was built from. */
    @Test
    void aPredicateOverWhatWasBuiltDividesThePositionItWasBuiltFrom() {
        PartitionEvidence kind = evidence("""
                module demo
                data Code = String
                    invariant String.length(value) <= 10
                data Known
                data Other
                data Nope
                behavior kind : (s: String) -> Known | Other | Nope
                    constructs Code
                let kind (s) = if Code(s) as c
                    then (if String.matches("[0-9]{4}", c.value) then Known else Other)
                    else Nope
                """, "kind");

        assertEquals(2, axis(kind, "s").classes().size(),
                () -> "the matching and the non-matching strings: " + axis(kind, "s").classes());
    }

    /**
     * A position below a recursive type, named through what was built, is one the reading has.
     *
     * <p>What the enumeration of a recursive type stops short of is there only where the body asks
     * for it, so a line there is drawn only where the demand followed the name to it. Held to the
     * line the same comparison draws where the name is bound by a {@code let}.
     */
    @Test
    void aPositionBelowARecursiveTypeNamedThroughWhatWasBuiltIsDemanded() {
        List<BoundaryTarget> throughTheAttempt = cutsOf("""
                module demo
                data Node = { v: Int, next: Option<Node> }
                data Wrap = { inner: Node, n: Int }
                    invariant n >= 0
                data A
                data B
                data Nope
                behavior f : (nd: Node, k: Int) -> A | B | Nope
                    constructs Wrap
                let f (nd, k) = {
                    guard Wrap { inner = nd, n = k } as w else Nope
                    match w.inner.next with
                        | Some m -> if m.v > 0 then A else B
                        | None -> B
                }
                """);
        List<BoundaryTarget> throughALet = cutsOf("""
                module demo
                data Node = { v: Int, next: Option<Node> }
                data A
                data B
                data Nope
                behavior f : (nd: Node, k: Int) -> A | B | Nope
                let f (nd, k) = {
                    let w = nd
                    match w.next with
                        | Some m -> if m.v > 0 then A else B
                        | None -> B
                }
                """);

        assertFalse(throughALet.isEmpty(), "the control draws the line");
        assertEquals(throughALet, throughTheAttempt);
    }

    private static List<BoundaryTarget> cutsOf(String source) {
        Compilation compilation = measured(source);
        Map<String, List<BorderAssessment>> all =
                Adequacy.readingsOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(all, "the model under test compiles");
        return all.get("f").stream().map(each -> each.border().cut()).toList();
    }

    /** A case declared unreachable inside {@code then} is claimed of the position it was built
     *  from. */
    @Test
    void anUnreachableCaseInsideWhatWasBuiltIsClaimed() {
        Compilation compilation = measured("""
                module demo
                data Red
                data Green
                data Color = Red | Green
                data W = { color: Color, n: Int }
                    invariant n >= 0
                data A
                data Nope
                behavior f : (c: Color, x: Int) -> A | Nope
                    constructs W
                let f (c, x) = if W { color = c, n = x } as w then (match w.color with
                    | Red -> A
                    | Green -> unreachable "never green") else Nope
                """);
        Bodies.Elaborated checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test compiles");
        Claims claims = checked.claims().get("f");

        assertEquals(List.of("c Green"), claims.all().stream()
                .map(Claims.Judged::claim)
                .map(WhatAnAttemptBuiltIsReadThroughItsNameTest::spelled)
                .toList());
    }

    private static String spelled(Claim claim) {
        return claim.at() + " " + claim.named().name();
    }

    /**
     * A line the type of what was built leaves no value at is one nothing arrives at, as it is
     * where a guard on the position rules the same values out.
     *
     * <p>Two environments meet here. Which position {@code b.value} is comes from the reading of
     * the input, and that nothing below 100 arrives there comes from what the type guarantees of
     * what was built; the answer is reached only where both are entered at {@code then}.
     */
    @Test
    void aLineTheBuiltTypeLeavesNoValueAtIsOneNothingArrivesAt() {
        PartitionEvidence throughTheAttempt = evidence("""
                module demo
                data Big = Int
                    invariant value >= 100
                data A
                data B
                data Nope
                behavior f : (x: Int) -> A | B | Nope
                    constructs Big
                let f (x) = if Big(x) as b then (if b.value > 10 then A else B) else Nope
                """, "f");
        PartitionEvidence underAGuard = evidence("""
                module demo
                data A
                data B
                data Nope
                behavior f : (x: Int) -> A | B | Nope
                let f (x) = {
                    guard x >= 100 else Nope
                    if x > 10 then A else B
                }
                """, "f");

        assertEquals(List.of("x NOTHING_ARRIVES_AT_THE_RULES_LINE"), spelled(underAGuard.notRead()),
                "the control");
        assertEquals(spelled(underAGuard.notRead()), spelled(throughTheAttempt.notRead()));
    }

    private static List<String> spelled(List<PartitionEvidence.NotRead> notRead) {
        return notRead.stream().map(each -> each.at() + " " + each.reason()).toList();
    }
}
