package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.check.AnalysisBody;
import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a run works out before a construction is read where the construction is not inside a
 * function value: on an arm, or on the right of an {@code ||}, past what decides it, which it
 * works out first; and whatever comes after it, a comparison among them, since a run that stops
 * there gets to none of it. The construction an attempt tests is none a run gets to and past,
 * since whether it is built is the attempt's deciding; what it is built of is.
 *
 * <p>Held here and not by the report: which runs take the arm is the way to the construction's to
 * say, and the report asks a value to meet it ({@link StopsOfABody}).
 */
class ARunGetsToAConstructionPastWhatDecidesItAndNotIntoAFunctionTest {

    private static final String HEAD = """
            module probe.w

            data Domain = String
                invariant String.matches("[a-z]+", value)

            data Named = { d: Domain }
                invariant String.length(d.value) > 1

            data Yes
            data No

            behavior pick : (s: String, t: String, u: Bool) -> Yes | No
                constructs CONSTRUCTED
            """;

    private static Core bodyOf(String body) {
        Compilation compilation = ACompiledModel.answered(HEAD.replace("CONSTRUCTED",
                body.contains("Named {") ? "Domain, Named" : "Domain") + "\n" + body);
        String module = compilation.modules().getFirst();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        AnalysisBody analysis = checked.analysisBodies().get("pick");
        assertNotNull(analysis, "the model under test writes pick");
        return analysis.core();
    }

    /** What a run works out before the one construction made of {@code t}, where that is read. */
    private static Optional<WhatARunWorksOutBeforeACount.BeforeAConstruction> toTheConstructionOfT(
            String body) {
        Core root = bodyOf(body);
        List<Core.Construct> ofT = new ArrayList<>();
        collect(root, ofT);
        assertEquals(1, ofT.size(), () -> "one construction of t is written: " + ofT);
        return WhatARunWorksOutBeforeACount.workedOutBeforeASite(root, ofT.getFirst());
    }

    private static void collect(Core e, List<Core.Construct> ofT) {
        Core here = Core.withoutStanding(e);
        if (here instanceof Core.Construct construct
                && Core.withoutStanding(construct.values().getFirst().value())
                instanceof Core.Read read && read.name().equals("t")) {
            ofT.add(construct);
        }
        Core.forEachChild(here, child -> collect(child, ofT));
    }

    @Test
    void aConstructionInTheValueOfALetIsGotTo() {
        assertTrue(toTheConstructionOfT("""
                let pick (s, t, u) = {
                    let made = Domain(t)
                    if s == "x" then Yes else No
                }
                """).isPresent());
    }

    /** A guard met after it decides nothing of whether it is got to. */
    @Test
    void aConstructionBeforeAGuardIsGotTo() {
        assertTrue(toTheConstructionOfT("""
                let pick (s, t, u) = {
                    let made = Domain(t)
                    if u then (if s == "x" then Yes else No) else No
                }
                """).isPresent());
    }

    /** What decides the arm is worked out on every run that gets to the construction, before
     *  what it is made of. */
    @Test
    void aConstructionOnAnArmIsGotToPastItsCondition() {
        assertEquals(List.of("u", "t"), namesWorkedOutFirst("""
                let pick (s, t, u) = {
                    let made = if u then Domain(t) else Domain("a")
                    if s == "x" then Yes else No
                }
                """));
    }

    @Test
    void aConstructionOnTheRightOfAnOrIsGotToPastItsLeft() {
        assertEquals(List.of("u", "t"), namesWorkedOutFirst("""
                let pick (s, t, u) = {
                    let ok = u || String.length(Domain(t).value) > 3
                    if s == "x" then Yes else No
                }
                """));
    }

    /** The names every run getting to the construction of {@code t} reads first, in order. */
    private static List<String> namesWorkedOutFirst(String body) {
        Optional<WhatARunWorksOutBeforeACount.BeforeAConstruction> before =
                toTheConstructionOfT(body);
        assertTrue(before.isPresent(), "a run gets to it");
        return before.get().onEveryRun().stream()
                .map(part -> ((Core.Read) Core.withoutStanding(part)).name()).toList();
    }

    @Test
    void aConstructionInAFunctionValueIsNotShownToBeGotTo() {
        assertEquals(Optional.empty(), toTheConstructionOfT("""
                let pick (s, t, u) = {
                    let made = List.map(w -> Domain(t), [s])
                    if s == "x" then Yes else No
                }
                """));
    }

    /** One worked out after a comparison is got to all the same: a run that stops there has
     *  got past the comparison, and gets to nothing after. */
    @Test
    void aConstructionAfterAComparisonIsGotTo() {
        assertTrue(toTheConstructionOfT("""
                let pick (s, t, u) = {
                    let same = s == "x"
                    let made = Domain(t)
                    if same then Yes else No
                }
                """).isPresent());
    }

    /** A refused attempt takes the other arm, so a run is neither stopped at the construction
     *  it tests nor shown to have got past it. */
    @Test
    void theConstructionAnAttemptTestsIsNoneARunGetsTo() {
        assertEquals(Optional.empty(), toTheConstructionOfT("""
                let pick (s, t, u) = {
                    let ok = if Domain(t) as d then true else false
                    if s == "x" then Yes else No
                }
                """));
    }

    /** What the construction an attempt tests is built of is worked out whenever the attempt
     *  is, and a construction there stops a run as any does. */
    @Test
    void aConstructionAnAttemptedOneIsBuiltOfIsGotTo() {
        assertTrue(toTheConstructionOfT("""
                let pick (s, t, u) = {
                    let ok = if Named { d = Domain(t) } as n then true else false
                    if s == "x" then Yes else No
                }
                """).isPresent());
    }
}
