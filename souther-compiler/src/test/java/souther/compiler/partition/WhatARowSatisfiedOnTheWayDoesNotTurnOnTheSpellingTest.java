package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a row had already satisfied when a comparison ran does not turn on how the condition was
 * spelled.
 *
 * <p>The region a border is searched in. {@code A && B} runs {@code B} only where {@code A} held,
 * and so does {@code if A then B else false} — one model, two spellings — so a row for a border on
 * {@code B} is looked for in the same place either way. Read off a condition found under a fork, the
 * second spelling narrowed and the first did not: the region for the same border came back as wide
 * as the declarations, which is where rows outside it are looked for as readily as inside.
 *
 * <p>Held between spellings rather than against cuts written down here. What they have to agree on
 * is what each comparison stands under, and a list repeated per spelling would go on holding if
 * every one of them established nothing.
 */
class WhatARowSatisfiedOnTheWayDoesNotTurnOnTheSpellingTest {

    private static final String MODEL = """
            module example.reach

            data Pair = { x: Int, y: Int }

            behavior conjoined : (p: Pair) -> Bool
            let conjoined (p) = p.x > 0 && p.y > 10

            behavior forked : (p: Pair) -> Bool
            let forked (p) = if p.x > 0 then p.y > 10 else false

            behavior namedThenForked : (p: Pair) -> Bool
            let namedThenForked (p) = {
                let high = p.x > 0
                if high then p.y > 10 else false
            }

            behavior disjoined : (p: Pair) -> Bool
            let disjoined (p) = p.x > 0 || p.y > 10

            behavior forkedTheOtherWay : (p: Pair) -> Bool
            let forkedTheOtherWay (p) = if p.x > 0 then true else p.y > 10

            behavior underACall : (p: Pair) -> Bool
            let underACall (p) = p.x > 0 && Int.max(p.y, 3) > 10

            behavior forkedUnderACall : (p: Pair) -> Bool
            let forkedUnderACall (p) =
                if p.x > 0 then Int.max(p.y, 3) > 10 else false
            """;

    /** What each comparison of {@code behavior} stands under, in no order and named by no site. */
    private static List<String> standingUnder(String behavior) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body);
        CoverageSites.Plan plan = CoverageSites.of(checked.behaviorBodies(), checked.decisions());
        Map<String, souther.compiler.inputs.InputDomain> inputs =
                compilation.db().ask(new Adequacy.Inputs(module)).value();
        GuardThresholds.Guards guards =
                GuardThresholds.of(behavior, body, plan, inputs.get(behavior), symbols);
        // By what the cuts say and not by which site they are filed under. Two spellings number
        // their comparisons differently and state the same thing.
        return guards.reaching().byComparison().values().stream()
                .map(Object::toString)
                .sorted()
                .toList();
    }

    /** The second comparison of a conjunction runs under the first, however the two are joined. */
    @Test
    void aConjunctionEstablishesWhatTheForkSpellingEstablishes() {
        assertEquals(standingUnder("forked"), standingUnder("conjoined"));
    }

    /**
     * And a fork on a name standing for the first establishes it too.
     *
     * <p>A condition read as a subtree of its own has no reading of the names above it, so the fork
     * was on something this had no words for and its arms proved nothing — while the same condition
     * written out proved the comparison. Which is the defect this whole issue is about, arriving
     * where the search for a row happens rather than where the line is drawn.
     */
    @Test
    void aForkOnANameEstablishesWhatTheNameStandsFor() {
        assertEquals(standingUnder("forked"), standingUnder("namedThenForked"));
    }

    /** The right of a disjunction runs where the left did not hold, however the two are joined. */
    @Test
    void aDisjunctionEstablishesWhatTheForkSpellingEstablishes() {
        assertEquals(standingUnder("forkedTheOtherWay"), standingUnder("disjoined"));
    }

    /**
     * And what stands reaches inside a shape this reading has no words for.
     *
     * <p>{@code A && f(B)} settles nothing about {@code f(B)} as a condition, and {@code B} inside
     * it still runs only where {@code A} held. Collected by folding over a reading of the condition,
     * the fold stopped at the shape it could not name and everything under it lost what stood.
     */
    @Test
    void whatStandsReachesInsideAConditionThisCannotRead() {
        assertEquals(standingUnder("forkedUnderACall"), standingUnder("underACall"));
    }
}
