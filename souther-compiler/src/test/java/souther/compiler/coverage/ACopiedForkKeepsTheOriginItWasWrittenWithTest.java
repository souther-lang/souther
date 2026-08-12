package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.check.TypeChecker;
import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.CoverageOrigin;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a fork carries about where it was written, which expansion must not change.
 *
 * <p>A non-recursive helper is spliced into each body that calls it, so one fork the author wrote
 * becomes several forks in the tree that runs. Those copies are what the emitter probes and what the
 * reachability analysis reasons about one at a time, and they are one thing to write rows for. The
 * origin is what says so, and it says it before anything is measured: nothing here reads a count.
 *
 * <p>These are about the tree, not about the report. What the report does with them is a separate
 * question and is asked where the measure is taken.
 */
class ACopiedForkKeepsTheOriginItWasWrittenWithTest {

    /** One three-arm helper, called once from one behavior and twice from another. */
    private static final String CALLED_TWICE = """
            module example.arms

            data Grade = Int
                invariant value >= 0

            data A
            data B
            data C
            data Band = A | B | C

            let rate (band: Band): Grade =
                match band with
                    | A -> Grade(1)
                    | B -> Grade(2)
                    | C -> Grade(3)

            data Left
            data Right
            data Side = Left | Right

            behavior twice : (side: Side, band: Band) -> Grade
                constructs Grade
            let twice (side, band) =
                match side with
                    | Left -> rate(band)
                    | Right -> rate(band)
            """;

    @Test
    void bothCopiesOfAHelpersForkCarryTheOneOriginItWasWrittenWith() {
        List<Core.Match> matches = matchesIn(bodyOf(CALLED_TWICE, "twice"));

        // The behavior's own `match side`, and one copy of `match band` per call of `rate`.
        assertEquals(3, matches.size(), "the expansion put a copy of the helper's fork at each call");
        CoverageOrigin own = matches.get(0).origin();
        CoverageOrigin first = matches.get(1).origin();
        CoverageOrigin second = matches.get(2).origin();

        assertEquals(first, second,
                "one `match` was written, so the two copies of it are one obligation");
        assertNotEquals(own, first,
                "and the fork the behavior wrote is not the fork the helper wrote");
    }

    /**
     * The case a position cannot answer. A helper of another module — the standard library here — has
     * its body stamped with the call site, so two copies of one of its forks are written at two
     * different places. Only the origin holds them together.
     */
    @Test
    void twoCallsOfOneLibraryHelperShareTheOriginAndNotThePosition() {
        Core body = bodyOf("""
                module example.two

                data Kept
                data Dropped
                data Mark = Kept | Dropped

                data Item = { mark: Mark }

                data Count = Int
                    invariant value >= 0

                behavior twoFilters : (items: List<Item>) -> Count
                    constructs Count, Kept, Dropped
                let twoFilters (items) =
                    Count(List.length(List.filter(i -> i.mark == Kept, items))
                        + List.length(List.filter(i -> i.mark == Dropped, items)))
                """, "twoFilters");

        List<Core.If> forks = ifsIn(body);
        assertEquals(2, forks.size(), "one fork per call of `List.filter`");
        assertEquals(forks.get(0).origin(), forks.get(1).origin(),
                "one fork is written in the library, and both calls copied that one");
        assertNotEquals(forks.get(0).pos(), forks.get(1).pos(),
                "while the positions are the two call sites, which is what a report shows");
    }

    /**
     * Why a content hash cannot stand in for this. Two forks made of the same thing are two
     * obligations where the author wrote them twice, and one where a helper holding one was called
     * twice — a difference nothing about their shape can see.
     */
    @Test
    void twoForksTheAuthorWroteSeparatelyHaveSeparateOrigins() {
        Core body = bodyOf("""
                module example.same

                data Grade = Int
                    invariant value >= 0

                data A
                data B
                data Band = A | B

                behavior both : (first: Band, second: Band) -> Grade
                    constructs Grade
                let both (first, second) =
                    match first with
                        | A ->
                            match second with
                                | A -> Grade(1)
                                | B -> Grade(2)
                        | B ->
                            match second with
                                | A -> Grade(1)
                                | B -> Grade(2)
                """, "both");

        List<Core.Match> matches = matchesIn(body);
        assertEquals(3, matches.size());
        Set<CoverageOrigin> origins = new LinkedHashSet<>();
        for (Core.Match m : matches) {
            origins.add(m.origin());
        }
        assertEquals(3, origins.size(),
                "the two inner `match`es are made of the same thing and are two obligations");
    }

    private static Core bodyOf(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        TypeChecker.Checked checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test compiles");
        Map<String, Core> bodies = checked.behaviorBodies();
        Core body = bodies.get(behavior);
        assertNotNull(body, "the behavior under test has a body");
        return body;
    }

    private static List<Core.Match> matchesIn(Core body) {
        List<Core.Match> out = new ArrayList<>();
        walk(body, e -> {
            if (e instanceof Core.Match m) {
                out.add(m);
            }
        });
        return out;
    }

    private static List<Core.If> ifsIn(Core body) {
        List<Core.If> out = new ArrayList<>();
        walk(body, e -> {
            if (e instanceof Core.If iff) {
                out.add(iff);
            }
        });
        return out;
    }

    /** Pre-order, so a fork is seen before the forks inside its arms. */
    private static void walk(Core e, java.util.function.Consumer<Core> f) {
        f.accept(e);
        Core.forEachChild(e, child -> walk(child, f));
    }
}
