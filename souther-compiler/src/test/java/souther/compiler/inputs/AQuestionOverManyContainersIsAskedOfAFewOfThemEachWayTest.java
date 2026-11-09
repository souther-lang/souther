package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A question over what many containers' elements add up to is asked of a few of them each way of
 * holding something or none, and of the rest as nothing says of them: the ways are two to the
 * power of the containers, and what the rest are asked as is wider and never narrower.
 *
 * <p>Twelve lists, and what all of them add up to: four thousand ways, of which the question is
 * asked of eight. The oracle for the answer is the row of twelve lists of none, which adds up to
 * nought.
 */
class AQuestionOverManyContainersIsAskedOfAFewOfThemEachWayTest {

    private static final int LISTS = 12;

    @Test
    void twelveListsAreAskedOfAFewWaysAndTheirTotalHoldsNought() {
        StringBuilder fields = new StringBuilder();
        for (int each = 0; each < LISTS; each++) {
            fields.append(each == 0 ? "" : ", ").append("x").append(each).append(": List<Int>");
        }
        Compilation compilation = Compilation.ofSources(List.of("""
                module g

                data Box = { %s }

                data Ok

                behavior counted : (b: Box) -> Ok
                """.formatted(fields)), ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading = RuleReadingContext.unshared(rules,
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        InputDomain input = InputDomain.of(compilation.db().ask(
                        new Bodies.DeclaredSignatures(module)).value().get("counted"), reading,
                TypeCardinality.Counts.workedOutIn(reading),
                souther.compiler.carrier.Membership.none());
        Map<NumericTerm, ExactRatio> every = new LinkedHashMap<>();
        for (int each = 0; each < LISTS; each++) {
            TermPath list = TermPath.of("b").then("x" + each);
            every.put(NumericTerm.TakenOf.asItStands(ValueName.Stdlib.operation("List", "sum"),
                    list, input.typeAt(list, rules), rules.inners(), rules.symbols()),
                    ExactRatio.ONE);
        }
        SearchRegion region = input.quantities(rules).region();
        long before = ReadQuantities.contextsRead();
        NumericDomain.Bounds total = assertInstanceOf(NumericDomain.FormProjection.Within.class,
                region.projectionOf(new LinearForm<>(ExactRatio.ZERO, every))).bounds();
        long read = ReadQuantities.contextsRead() - before;
        assertTrue(total.admits(Count.of(0)), total.toString());
        assertTrue(read <= 16, "contexts read: " + read);
        List<NumericTerm> terms = new ArrayList<>(every.keySet());
        assertTrue(region.given(Map.of(terms.getFirst(), Count.of(0))).emptiness().isEmpty(),
                "a list of none is a row");
    }

    /**
     * An emptiness shown of the containers that bear on it is shown beside any number of others
     * that do not, in whatever order the fixed terms are held in: it is the containers that are
     * asked about and not the first few of them. {@code x0} holds none whatever it is, so a total
     * of five over it is no row; the lists beside it are held to nought, which any of them holds.
     */
    @Test
    void anEmptinessIsShownBesideContainersNothingRelatesToItInAnyOrder() {
        for (boolean relatedFirst : new boolean[] {true, false}) {
            for (int unrelated : new int[] {0, 2, 3, 5, 7}) {
                StringBuilder fields = new StringBuilder("x0: List<Int>");
                for (int each = 1; each <= unrelated; each++) {
                    fields.append(", x").append(each).append(": List<Int>");
                }
                Compilation compilation = Compilation.ofSources(List.of("""
                        module g

                        data Box = { %s }
                            invariant none = List.length(x0) == 0

                        data Ok

                        behavior counted : (b: Box) -> Ok
                        """.formatted(fields)), ModulePath.EMPTY);
                String module = compilation.modules().get(0);
                RuleReadingSource rules = RuleReadings.of(compilation, module);
                RuleReadingContext reading = RuleReadingContext.unshared(rules,
                        ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
                InputDomain input = InputDomain.of(compilation.db().ask(
                                new Bodies.DeclaredSignatures(module)).value().get("counted"),
                        reading, TypeCardinality.Counts.workedOutIn(reading),
                        souther.compiler.carrier.Membership.none());
                Map<NumericTerm, Place> fixed = new LinkedHashMap<>();
                for (int step = 0; step <= unrelated; step++) {
                    int each = relatedFirst ? step : unrelated - step;
                    TermPath list = TermPath.of("b").then("x" + each);
                    fixed.put(NumericTerm.TakenOf.asItStands(
                                    ValueName.Stdlib.operation("List", "sum"), list,
                                    input.typeAt(list, rules), rules.inners(), rules.symbols()),
                            Count.of(each == 0 ? 5 : 0));
                }

                assertTrue(!input.quantities(rules).region().given(fixed).emptiness().isEmpty(),
                        "x0 summing to five is no row, beside " + unrelated + " lists fixed to"
                                + " nought, " + (relatedFirst ? "x0 first" : "x0 last"));
            }
        }
    }
}
