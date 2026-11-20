package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.check.AnalysisBody;
import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.BinOp;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Every run that takes the arms the way to a comparison takes gets to a construction, unless
 * something before ends it, only where nothing on the way from where the two part decides whether
 * the construction is worked out, and it is worked out before the comparison: no arm, no right of
 * an {@code ||}, no function value. The construction an attempt tests ends no run, and is told
 * apart from both.
 *
 * <p>Held here and not by the report: what a construction on such a part asks is read under what
 * decides it, and no model reaches the report with a construction there whose condition is left.
 */
class ARunOnTheWayGetsToAConstructionOnlyWhereNothingDecidesItTest {

    private static final String HEAD = """
            module probe.w

            data Domain = String
                invariant String.matches("[a-z]+", value)

            data Yes
            data No

            behavior pick : (s: String, t: String, u: Bool) -> Yes | No
                constructs Domain
            """;

    private static Core bodyOf(String body) {
        Compilation compilation = ACompiledModel.answered(HEAD + "\n" + body);
        String module = compilation.modules().getFirst();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        AnalysisBody analysis = checked.analysisBodies().get("pick");
        assertNotNull(analysis, "the model under test writes pick");
        return analysis.core();
    }

    /** What is known of a run on the way to the one comparison of equality getting to the one
     *  construction made of {@code t}. */
    private static WhatARunWorksOutBeforeACount.ToAConstruction toTheConstructionOfT(String body) {
        Core root = bodyOf(body);
        List<Core> comparisons = new ArrayList<>();
        List<Core.Construct> ofT = new ArrayList<>();
        collect(root, comparisons, ofT);
        assertEquals(1, comparisons.size(), () -> "one comparison is written: " + comparisons);
        assertEquals(1, ofT.size(), () -> "one construction of t is written: " + ofT);
        return WhatARunWorksOutBeforeACount.toAConstruction(root, comparisons.getFirst(),
                ofT.getFirst());
    }

    private static void collect(Core e, List<Core> comparisons, List<Core.Construct> ofT) {
        Core here = Core.withoutStanding(e);
        if (here instanceof Core.Binary binary && binary.op() == BinOp.EQ) {
            comparisons.add(binary);
        }
        if (here instanceof Core.Construct construct
                && Core.withoutStanding(construct.values().getFirst().value())
                instanceof Core.Read read && read.name().equals("t")) {
            ofT.add(construct);
        }
        Core.forEachChild(here, child -> collect(child, comparisons, ofT));
    }

    @Test
    void aConstructionInTheValueOfALetBeforeTheComparisonIsGotTo() {
        assertInstanceOf(WhatARunWorksOutBeforeACount.BeforeAConstruction.class,
                toTheConstructionOfT("""
                        let pick (s, t, u) = {
                            let made = Domain(t)
                            if s == "x" then Yes else No
                        }
                        """));
    }

    /** A guard met after it decides nothing of whether it is got to. */
    @Test
    void aConstructionBeforeAGuardTheComparisonIsUnderIsGotTo() {
        assertInstanceOf(WhatARunWorksOutBeforeACount.BeforeAConstruction.class,
                toTheConstructionOfT("""
                        let pick (s, t, u) = {
                            let made = Domain(t)
                            if u then (if s == "x" then Yes else No) else No
                        }
                        """));
    }

    @Test
    void aConstructionOnAnArmOfAValueBeforeTheComparisonIsNotShownToBeGotTo() {
        assertInstanceOf(WhatARunWorksOutBeforeACount.ToAConstruction.NotShown.class,
                toTheConstructionOfT("""
                        let pick (s, t, u) = {
                            let made = if u then Domain(t) else Domain("a")
                            if s == "x" then Yes else No
                        }
                        """));
    }

    @Test
    void aConstructionOnTheRightOfAnOrIsNotShownToBeGotTo() {
        assertInstanceOf(WhatARunWorksOutBeforeACount.ToAConstruction.NotShown.class,
                toTheConstructionOfT("""
                        let pick (s, t, u) = {
                            let ok = u || String.length(Domain(t).value) > 3
                            if s == "x" then Yes else No
                        }
                        """));
    }

    @Test
    void aConstructionInAFunctionValueIsNotShownToBeGotTo() {
        assertInstanceOf(WhatARunWorksOutBeforeACount.ToAConstruction.NotShown.class,
                toTheConstructionOfT("""
                        let pick (s, t, u) = {
                            let made = List.map(w -> Domain(t), [s])
                            if s == "x" then Yes else No
                        }
                        """));
    }

    /** One worked out after the comparison is not on the way to it. */
    @Test
    void aConstructionAfterTheComparisonIsNotShownToBeGotTo() {
        assertInstanceOf(WhatARunWorksOutBeforeACount.ToAConstruction.NotShown.class,
                toTheConstructionOfT("""
                        let pick (s, t, u) = {
                            let same = s == "x"
                            let made = Domain(t)
                            if same then Yes else No
                        }
                        """));
    }

    @Test
    void theConstructionAnAttemptTestsIsToldApart() {
        assertInstanceOf(WhatARunWorksOutBeforeACount.ToAConstruction.Attempted.class,
                toTheConstructionOfT("""
                        let pick (s, t, u) = {
                            let ok = if Domain(t) as d then true else false
                            if s == "x" then Yes else No
                        }
                        """));
    }
}
