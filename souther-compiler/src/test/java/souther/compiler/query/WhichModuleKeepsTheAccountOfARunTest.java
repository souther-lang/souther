package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Which module keeps an account of a run, when the line and the end that stops it were written in
 * different modules.
 *
 * <p>A module has an account of a point where it reads the point and its own declarations are among
 * what settled it. Both halves matter. A module that only carries a type answers for none of its
 * rules — what it exercises of a type it depends on is a measure and not a debt (issue #1077) — and
 * a module whose record takes an imported position in has put an end there, so the run stopping at
 * that end is its own to answer for however wrote the line beside it.
 *
 * <p>Decided from what settled the point rather than from the line it is a point of. Asked of the
 * line, the second of those was accounted nowhere: the module that wrote the line never reads the
 * narrowed position, and the module that narrowed it does not own the line.
 */
class WhichModuleKeepsTheAccountOfARunTest {

    /** A type with a floor, and nothing else. */
    private static final String PRODUCER = """
            module example.producer exposing ( Cap )

            data Cap = Int
                invariant floor = value >= 0
            """;

    /** A module of its own that only carries the imported type. */
    private static final String CARRIER = """
            module example.carrier

            import example.producer (Cap)

            data Holds = { c: Cap }

            behavior take : (h: Holds) -> Int
            let take (h) = 1

            example take
                | "x" : (Holds { c = Cap(1) }) -> 1
            """;

    /** A module whose own record takes the imported position in. */
    private static final String NARROWER = """
            module example.narrower

            import example.producer (Cap)

            data Lim = Int
                invariant capped = value <= 50

            data Held = { c: Cap, l: Lim }
                invariant tight = c.value <= l.value

            behavior take : (h: Held) -> Int
            let take (h) = 1

            example take
                | "x" : (Held { c = Cap(1), l = Lim(2) }) -> 1
            """;

    /**
     * A module that took an imported position in answers for the run that stops there.
     *
     * <p>{@code Cap} drew the line and {@code example.narrower} put the end the run above it stops
     * at, so the row somebody has to write inside that run is a row of this module's making. The
     * account is here because the point is read here and this module's declaration is among what
     * settled it.
     */
    @Test
    void aModuleThatTookThePositionInAnswersForTheRun() {
        List<Adequacy.DeclaredDebt> debts = debtsOf(compiled(PRODUCER, NARROWER),
                "example.narrower");
        // The line is `Cap`'s floor, which this module did not write; the end the run stops at is
        // where this module's record takes the position in. Its own `Lim` owes lines of its own,
        // which is not what this is about.
        List<Adequacy.DeclaredDebt> aboveTheFloor = debts.stream()
                .filter(each -> each.debt().said().equals("value in 0 < value <= 50")).toList();

        assertEquals(1, aboveTheFloor.size(),
                () -> "the run above the imported floor is one debt here: " + said(debts));
        assertEquals("Held", aboveTheFloor.get(0).subject().named(),
                "and it is this module's own declaration that is told about it, not the one that"
                        + " wrote the line");
    }

    /**
     * A module that only carries the type answers for nothing.
     *
     * <p>Nothing here moved anything about {@code Cap}, so there is no row this module's author can
     * be asked to write on the strength of {@code Cap}'s rules. What this module exercises of a type
     * it depends on is a different question and is not a debt.
     */
    @Test
    void aModuleThatOnlyCarriesTheTypeAnswersForNothing() {
        assertEquals(List.of(), said(debtsOf(compiled(PRODUCER, CARRIER), "example.carrier")),
                "the carrier wrote none of the rules and moved none of the ends");
    }

    /**
     * And the module that wrote the line keeps its own account, of the readings it has.
     *
     * <p>Which is none here: {@code example.producer} declares no behavior, so it reads the line
     * nowhere. A debt is a line one module's declarations owe and one of its behaviors reads, and
     * the second half is what stops a module being told about work it cannot do (issue #1077).
     */
    @Test
    void theModuleThatWroteTheLineAnswersOnlyForWhatItReads() {
        assertEquals(List.of(), said(debtsOf(compiled(PRODUCER, NARROWER), "example.producer")),
                "nothing here reads the line, so nothing here is short a row at it");
    }

    private static List<String> said(List<Adequacy.DeclaredDebt> debts) {
        return debts.stream().map(each -> each.debt().role() + " " + each.debt().said()).toList();
    }

    private static List<Adequacy.DeclaredDebt> debtsOf(Compilation compilation, String module) {
        List<Adequacy.DeclaredDebt> debts =
                compilation.db().ask(new Adequacy.DeclaredBorders(module)).value();
        assertNotNull(debts, "the model under test compiles");
        return debts;
    }

    private static Compilation compiled(String... sources) {
        Compilation compilation = Compilation.ofSources(List.of(sources), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.db().allReports().stream()
                        .filter(each -> each.report().isError())
                        .map(each -> each.report().diagnostic().code()).toList(),
                "the model under test compiles");
        return compilation;
    }
}
