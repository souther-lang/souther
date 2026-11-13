package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.TestDay;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.carrier.Membership;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the elements of a container add up to is asked of the container holding something and of
 * it holding none, where nothing says which: over none it is what the walk starts from, whatever
 * the rules of an element say.
 *
 * <p>The oracle is the list of none, a row of every one of these models, which adds up to nought.
 */
class AWalkOverAContainerHoldingNoneComesToWhereItStartsTest {

    /** The region of {@code source}'s behavior, its list at {@code path}, and what that list's
     *  numbers at {@code field} add up to. */
    private record Read(SearchRegion region, NumericTerm total, NumericTerm counted) {}

    private static Read read(String source, String path, String field) {
        return read(ACompiledModel.compiles(
                Compilation.ofSources(List.of(source), ModulePath.EMPTY)), path, field);
    }

    /** The same of a model that is refused for {@code refusedFor}, which is read all the same. */
    private static Read readRefused(String source, String path, String field,
                                    List<String> refusedFor) {
        return read(ACompiledModel.refusedWith(refusedFor,
                Compilation.ofSources(List.of(source), ModulePath.EMPTY)), path, field);
    }

    private static Read read(Compilation compilation, String path, String field) {
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading = RuleReadingContext.unshared(rules,
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        InputDomain input = InputDomain.of(compilation.db().ask(
                        new Bodies.DeclaredSignatures(module)).value().get("counted"), reading,
                TypeCardinality.Counts.workedOutIn(reading), Membership.none());
        TermPath xs = input.positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(path)).findFirst().orElseThrow();
        TermPath at = field == null ? xs.element() : xs.element().then(field);
        NumericTerm total = NumericTerm.TakenOver.of(ValueName.Stdlib.operation("List", "sum"),
                new RunSource.ProjectedOccurrences(at), Type.INT, rules.inners(),
                rules.symbols());
        NumericTerm counted = NumericTerm.TakenOf.asItStands(
                ValueName.Stdlib.operation("List", "length"), xs, input.typeAt(xs, rules),
                rules.inners(), rules.symbols());
        return new Read(input.quantities(rules).region(), total, counted);
    }

    /** A list held to none adds up to nought and to nothing else. */
    @Test
    void aListThatCanOnlyBeEmptyComesToNought() {
        Read read = read("""
                module g

                data Box = { xs: List<Int> } invariant List.length(xs) <= 0

                data Ok

                behavior counted : (b: Box) -> Ok
                """, "b.xs", null);
        Endpoint nought = Endpoint.inclusive(Count.of(0));
        assertEquals(new NumericDomain.FormProjection.Within(
                        new NumericDomain.Bounds(nought, nought)),
                read.region().projectionOf(read.total()));
    }

    /** The list of none, with what it adds up to standing, is a row of a list nothing is said
     *  of. */
    @Test
    void theListOfNoneIsARowOfAListNothingIsSaidOf() {
        Read read = read("""
                module g

                data Box = { xs: List<Int> } invariant List.length(xs) >= 0

                data Ok

                behavior counted : (b: Box) -> Ok
                """, "b.xs", null);
        assertTrue(read.region().given(Map.of(read.total(), Count.of(0), read.counted(),
                Count.of(0))).emptiness().isEmpty());
    }

    /** Where no element can be, the list of none still adds up to nought. */
    @Test
    void whereNoElementCanBeTheTotalIsStillNought() {
        Read read = readRefused("""
                module g

                data P = { n: Int } invariant n > 10 && n < 0

                data Ok

                behavior counted : (xs: List<P>) -> Ok
                """, "xs", "n", List.of("E1013"));
        NumericDomain.Bounds total = assertInstanceOf(NumericDomain.FormProjection.Within.class,
                read.region().projectionOf(read.total())).bounds();
        assertTrue(total.admits(Count.of(0)), total.toString());
    }
}
