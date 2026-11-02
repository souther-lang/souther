package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.BinOp;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a run works out to reach a comparison in an arm of an attempt to build a value is what the
 * construction is built of, and not the construction.
 *
 * <p>An attempt takes the other arm where the construction is refused and ends no run, which is
 * what a plain construction does not: one that is refused ends the run. So the construction of an
 * attempt is not among what is worked out to reach its arm, while what it is built of is, and a
 * construction written beside it is.
 */
class WhatARunWorksOutToReachAnAttemptsArmTest {

    private static final String HEAD = """
            module probe.w

            data Domain = String
                invariant String.matches("[a-z]+", value)

            data Yes
            data No

            behavior pick : (s: String, t: String) -> Yes | No
                constructs Domain
            """;

    /** The tree of {@code pick}, written {@code body}. */
    private static Core bodyOf(String body) {
        Compilation compilation = Compilation.ofSource(HEAD + "\n" + body, "Main");
        String module = compilation.modules().getFirst();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        AnalysisBody analysis = checked.analysisBodies().get("pick");
        assertNotNull(analysis, "the model under test writes pick");
        return analysis.core();
    }

    /** The one comparison of equality the tree holds. */
    private static Core.Binary theComparison(Core root) {
        List<Core.Binary> found = new ArrayList<>();
        collect(root, found);
        assertEquals(1, found.size(), () -> "one comparison is written: " + found);
        return found.getFirst();
    }

    private static void collect(Core e, List<Core.Binary> into) {
        if (Core.withoutStanding(e) instanceof Core.Binary binary && binary.op() == BinOp.EQ) {
            into.add(binary);
        }
        Core.forEachChild(Core.withoutStanding(e), child -> collect(child, into));
    }

    private static List<Core> workedOut(String body) {
        Core root = bodyOf(body);
        return WhatARunWorksOutBeforeACount.alwaysWorkedOutUpTo(root, theComparison(root));
    }

    private static boolean holdsAConstruction(List<Core> parts) {
        return parts.stream().anyMatch(part -> Core.withoutStanding(part) instanceof Core.Construct);
    }

    @Test
    void theConstructionAnAttemptTestsIsNotWorkedOutToReachItsArm() {
        List<Core> parts = workedOut("""
                let pick (s, t) = if Domain(s) as d then (if t == "x" then Yes else No) else No
                """);
        assertTrue(!holdsAConstruction(parts), parts::toString);
    }

    @Test
    void whatTheConstructionAnAttemptTestsIsBuiltOfIsWorkedOutToReachItsArm() {
        List<Core> parts = workedOut("""
                let pick (s, t) = if Domain(s) as d then (if t == "x" then Yes else No) else No
                """);
        assertTrue(parts.stream().anyMatch(part -> Core.withoutStanding(part)
                instanceof Core.Read read && read.name().equals("s")), parts::toString);
    }

    @Test
    void aConstructionWrittenBesideAnAttemptIsWorkedOut() {
        List<Core> parts = workedOut("""
                let pick (s, t) = {
                    let made = Domain(t)
                    if Domain(s) as d then (if t == "x" then Yes else No) else No
                }
                """);
        assertTrue(holdsAConstruction(parts), parts::toString);
    }
}
