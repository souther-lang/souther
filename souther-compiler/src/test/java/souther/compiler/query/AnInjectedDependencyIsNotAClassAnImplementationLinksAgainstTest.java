package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Severity;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.RowOutcome;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a behavior depends on is handed to it, and what it calls it constructs.
 *
 * <p>The emitter says of one call that "neither is a question about what the call reaches": a callee
 * implemented elsewhere is constructed, and one supplied to the class being emitted is read off a
 * field. Only the first is a class that has to be in the image for this one to run.
 *
 * <p>So an implementation nothing made takes its callers with it and leaves the behaviors that
 * depend on it standing. Their rows supply what they depend on themselves, and a row that could run
 * against a stand-in is a row whose finding is a gap rather than an uncertainty — which is the whole
 * of what this change is about.
 */
class AnInjectedDependencyIsNotAClassAnImplementationLinksAgainstTest {

    /**
     * A module whose implemented behavior is refused by its own invariant.
     *
     * <p>{@code %s} is what its construction of an {@code Id} states, so the two readings below
     * differ in that and in nothing else. What {@code load} answers goes in the field beside it,
     * which is what makes the dependency one the body uses.
     *
     * <p>It is implemented here and depended on elsewhere, which is what makes the two kinds of
     * reference tell apart. The language allows that only of a behavior that itself depends on
     * something — one that depends on nothing is reached by name instead — so {@code load} is here
     * for {@code fetch} to be injectable at all.
     */
    private static final String SUPPLIER = """
            module example.supplier exposing ( Id, Row, Person, load, fetch )

            data Id = Int
                invariant value >= 1

            data Row = { id: Id }
            data Person = { id: Id, seen: Row }

            behavior load : (id: Id) -> Row

            behavior fetch : (id: Id) -> Person
                depends on load
                constructs Person, Id
            let fetch (id, load) = Person { id = Id(%s), seen = load(id) }
            """;

    /**
     * One behavior that depends on it and one that calls it.
     *
     * <p>Both name the same implementation and only the second is a class that has to be there. The
     * caller is here so that a reading which took nothing away at all would be caught: it must go
     * with the implementation it constructs.
     */
    private static final String CONSUMER = """
            module example.consumer

            import example.supplier ( Id, Row, Person, fetch )

            data Order = { by: Id }
            data Placed = { by: Id }

            behavior place : (o: Order) -> Placed
                depends on fetch
                constructs Placed
            let place (o, fetch) = Placed { by = fetch(o.by).id }

            let stood = Person { id = Id(1), seen = Row { id = Id(1) } }

            example place
                | "one" : (Order { by = Id(1) }) with fetch = stood -> Placed { by = Id(1) }
            """;

    /** What this compiler refuses a construction its own invariant rejects. */
    private static final String THE_REFUSED_CONSTRUCTION = "E2010";

    /**
     * Where everything came out, both of them may be run.
     *
     * <p>Here so the reading below is a difference. Answered the same whatever the model, a reading
     * that took nothing away would pass on its own.
     */
    @Test
    void whereEverythingCameOutBothMayBeRun() {
        Compiled clean = compile("1");

        assertEquals(List.of(), clean.refusals(),
                () -> "nothing is refused about this model, and it was refused about "
                        + clean.refusals());
        assertEquals(Set.of("fetch"), clean.runnable("example.supplier"));
        assertEquals(Set.of("place"), clean.runnable("example.consumer"));
    }

    /**
     * A refused implementation takes the behavior that calls it and leaves the one that depends on
     * it.
     *
     * <p>The two stand in one module, so nothing about the module or the compile tells them apart —
     * only which kind of reference each makes.
     */
    @Test
    void aRefusedImplementationTakesItsCallerAndLeavesWhatDependsOnIt() {
        Compiled refused = compile("0");

        assertEquals(List.of(THE_REFUSED_CONSTRUCTION), refused.refusals(),
                () -> "this model is refused about the construction alone, and it was refused"
                        + " about " + refused.refusals());
        assertEquals(Set.of(), refused.runnable("example.supplier"));
        assertEquals(Set.of("place"), refused.runnable("example.consumer"),
                "`place` is handed what it depends on rather than constructing it");
    }

    /**
     * And its row runs, against the stand-in the row wrote.
     *
     * <p>What makes the answer above worth having. A row of a behavior that may be run is observed,
     * and what it is observed against for the dependency is what the row states — so an
     * implementation nobody could make in the module it depends on is not the row's business.
     */
    @Test
    void andItsRowIsObservedAgainstTheStandInTheRowWrote() {
        Compiled refused = compile("0");

        List<RowOutcome> ran = new ArrayList<>(refused.compilation().db()
                .ask(new Output.RowsRead("example.consumer")).value()
                .byBehavior().get("place").ran());

        assertEquals(1, ran.size(), () -> "the row written for `place` is what this reads: " + ran);
        assertEquals(Disposition.HELD, ran.getFirst().disposition(),
                () -> "the row ran and held: " + ran.getFirst());
    }

    /** A compilation of the model, and the answers this asks of it. */
    private record Compiled(Compilation compilation) {

        Set<String> runnable(String module) {
            Answer<Bodies.Implementations> answer =
                    compilation.db().ask(new Bodies.RunnableImplementations(module));
            assertTrue(answer.present(), "a module that settled is one this answers about");
            return answer.value().runnable();
        }

        List<String> refusals() {
            return compilation.diagnostics().values().stream()
                    .flatMap(List::stream)
                    .filter(each -> each.diagnostic().severity() == Severity.ERROR)
                    .map(each -> each.diagnostic().code().toString())
                    .sorted()
                    .toList();
        }
    }

    private static Compiled compile(String constructs) {
        Compilation compilation = Compilation.ofSources(
                List.of(SUPPLIER.formatted(constructs), CONSUMER), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return new Compiled(compilation);
    }
}
