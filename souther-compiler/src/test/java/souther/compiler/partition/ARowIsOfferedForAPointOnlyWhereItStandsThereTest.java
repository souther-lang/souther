package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.InputDomain;
import souther.compiler.numeric.Count;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A row is offered for a point only where the value that was built stands there.
 *
 * <p>What was asked for and what was built are two things, and the generator answered with the
 * first. A row composed to put a term at a number went out labelled for that number whatever the
 * value came to — so a row that reached the point and a row that did not were reported alike, as
 * {@code Generated}, and an author reading the report was told a shortfall had been answered when
 * it had not (issue #1063).
 *
 * <p><b>Held against a construction that answers with something else, because that is the case the
 * check is for.</b> {@code TermRealizations} states of itself that every value built there reads
 * back as the number it was built for, and names the way it would break: "a row offered at an edge
 * it does not stand on". The generator's own arithmetic meeting that is what the other tests here
 * are about; this one is about what happens when something between the candidate and the value does
 * not — a decoder that narrows, a construction that clamps — which is exactly what nothing was
 * asking.
 */
class ARowIsOfferedForAPointOnlyWhereItStandsThereTest {

    private static final String BOUNDED = """
            module example.bounded

            data Amount = Int
                invariant value >= 0 && value <= 100
            data Req = { cost: Amount }
            data Res = { n: Int }

            behavior f : (r: Req) -> Res
            """;

    /**
     * A construction that answers with a value away from the point offers no row for it.
     *
     * <p>And says which of the two it is: nothing was refused by the model, so reporting it as a
     * value the rules turned away would send an author looking at their invariant.
     */
    @Test
    void aValueThatLandsElsewhereIsNoWitness() {
        Generator.BoundaryAttempt attempt = attemptAt(Count.of(100), always(7));

        Generator.BoundaryAttempt.Unresolved no = assertInstanceOf(
                Generator.BoundaryAttempt.Unresolved.class, attempt,
                "a value that reads back at 7 is no row for the point at 100");
        assertEquals(Generator.UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS,
                no.why().reason());
    }

    /** And one that answers with the value it was built for is the row. */
    @Test
    void aValueThatLandsOnThePointIsTheWitness() {
        Generator.BoundaryAttempt attempt = attemptAt(Count.of(100), always(100));

        Generator.BoundaryAttempt.Built built = assertInstanceOf(
                Generator.BoundaryAttempt.Built.class, attempt,
                "a value that reads back at 100 stands at the point");
        assertEquals(List.of("Req { cost = Amount(100) }"),
                built.row().inputs().stream().map(FixtureTemplate::text).toList());
    }

    /**
     * And where nothing built the candidate, the row is offered as it was composed.
     *
     * <p>The fail-open half, and the reason it is one: there is no runtime to put a candidate
     * through, so nothing here can say where it went — and refusing every row wherever a build is
     * unavailable would answer a question nobody asked with the worst of the two answers.
     */
    @Test
    void whereNothingBuiltItTheRowIsOfferedAsComposed() {
        assertInstanceOf(Generator.BoundaryAttempt.Built.class,
                attemptAt(Count.of(100), Generator.CandidateCheck.ANY),
                "nothing ran the candidate, so nothing says it stands anywhere else");
    }

    /** Two parameters, and a second position under the first so its search has more than one
     *  candidate to offer — which is what lets a parameter refuse one and still succeed. */
    private static final String TWO = """
            module example.bounded

            data Amount = Int
                invariant value >= 0 && value <= 100
            data Req = { cost: Amount, note: String }
            data Other = { n: Int }
            data Res = { n: Int }

            behavior g : (r: Req, o: Other) -> Res
            """;

    /**
     * What one parameter's search found out is not said of another's.
     *
     * <p>A candidate turned away for standing elsewhere is news about the parameter it was built
     * for. Kept for the whole row, the first parameter certifying its second candidate would name
     * the reason a later parameter failed for — and the later one was refused by the model, which is
     * the opposite answer: one says every value the rules allow was turned away, and the other says
     * what was built did not stand where it was built for.
     */
    @Test
    void whatOneParametersSearchFoundOutIsNotSaidOfAnothers() {
        int[] tried = {0};
        Generator.BoundaryAttempt attempt = attemptOver(TWO, "g", Count.of(100),
                (parameter, _) -> {
                    if (parameter != 0) {
                        return new Generator.CandidateCheck.Built.Refused("the model refuses it");
                    }
                    // The first candidate stands away from the point and the next stands on it, so
                    // this parameter refuses one and succeeds all the same.
                    return new Generator.CandidateCheck.Built.Value(
                            reqWith(++tried[0] == 1 ? 7 : 100));
                });

        Generator.BoundaryAttempt.Unresolved no = assertInstanceOf(
                Generator.BoundaryAttempt.Unresolved.class, attempt,
                "no value of `o` was allowed, so no row builds");
        assertEquals(Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED,
                no.why().reason(),
                "the second parameter's every candidate was refused by the model, which the first"
                        + " parameter's uncertified candidate says nothing about");
    }

    /** A check answering every candidate with a {@code Req} whose cost is {@code n}, whatever was
     *  asked for — a construction that does not answer with what it was given. */
    private static Generator.CandidateCheck always(int n) {
        return (_, _) -> new Generator.CandidateCheck.Built.Value(reqWith(n));
    }

    private static ObservedValue reqWith(int n) {
        return new ObservedValue.Constructed(declared("Req"), Map.of("cost",
                new ObservedValue.Constructed(declared("Amount"),
                        Map.of("value", new ObservedValue.Integer(n))),
                "note", new ObservedValue.Text("")));
    }

    private static souther.compiler.types.TypeSymbol declared(String name) {
        return souther.compiler.types.TypeSymbols.declared(
                new souther.compiler.types.TypeKey("example.bounded", name));
    }

    private static Generator.BoundaryAttempt attemptAt(souther.compiler.numeric.Place at,
                                                       Generator.CandidateCheck check) {
        return attemptOver(BOUNDED, "f", at, check);
    }

    private static Generator.BoundaryAttempt attemptOver(String source, String behavior,
                                                         souther.compiler.numeric.Place at,
                                                         Generator.CandidateCheck check) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(each -> each.name().equals(behavior)).findFirst().orElseThrow();
        InputDomain domain = compilation.db()
                .ask(new souther.compiler.query.Adequacy.Inputs(module)).value().get(spec.name());
        assertNotNull(domain, "the model under test compiles");
        Partitions.Partitioning partitioning =
                Partitions.of(spec.name(), domain, symbols, ReadAs.THE_COMPILATION_DOES);

        List<String> names = new ArrayList<>();
        spec.params().forEach(each -> names.add(each.name()));
        MeasuredInput subject =
                MeasuredInput.of(spec.name(), domain.reading(symbols), partitioning.axes());

        Axis axis = partitioning.axes().stream()
                .filter(each -> each.path().toString().equals("r.cost")).findFirst().orElseThrow();
        return Generator.probeFixing(subject, "r.cost = " + at,
                _ -> axis.term().answeredOn(axis.type(), symbols),
                Map.of(new RealizationTarget.AtOnePosition(axis.term()), at),
                Reachability.untouched(domain.quantities(symbols).region()), check);
    }
}
