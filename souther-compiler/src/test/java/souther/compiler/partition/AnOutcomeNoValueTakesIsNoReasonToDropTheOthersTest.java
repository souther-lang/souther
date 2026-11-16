package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.Compiler;
import souther.compiler.check.RuleReadings;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.reading.CoverageRead;
import souther.compiler.reading.Decision;
import souther.compiler.reading.Factor;
import souther.compiler.reading.Interaction;
import souther.compiler.reading.Outcome;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A group is a way in and what varies at it, one factor for each value consumed there, and a
 * factor is the ways its value comes about. A way no value takes — its decisions state cases of
 * one position that are apart — is no combination a row could be in, and it is no reason to lose
 * the ways of the same factor that some value does take: their combinations with the other
 * factors are as owed as they were before it was written.
 */
class AnOutcomeNoValueTakesIsNoReasonToDropTheOthersTest {

    private static final String TOTAL = """
            module example.apart

            data A
            data B
            data C
            data Kind = A | B | C

            data On
            data Off
            data Flag = On | Off

            data Fee = Int
                invariant value >= 0

            behavior total : (k: Kind, f: Flag) -> Fee
                constructs Fee

            let total (k, f) = Fee((match k with
                                        | A -> 1
                                        | B -> 2
                                        | C -> 3)
                                    + (match f with
                                        | On -> 10
                                        | Off -> 0))
            """;

    private record Read(Interaction group, MeasuredInput.MeasuredAxes axes) {}

    private static Read read() {
        var compilation = ACompiledModel.compiles(Compiler.analyzedModules(List.of(TOTAL),
                ModulePath.EMPTY, new ArrayList<>(), Adequacy.Asked.fullReport()));
        CoverageRead.Read meets = compilation.db()
                .ask(new Adequacy.Meets("example.apart")).value().get("total");
        MeasuredInput.MeasuredAxes axes = MeasuredInput.of("total",
                compilation.db().ask(new Adequacy.Inputs("example.apart")).value().get("total")
                        .reading(RuleReadings.of(compilation, "example.apart")),
                compilation.db().ask(new Adequacy.Divided("example.apart", "total")).value())
                .axes();
        assertEquals(1, meets.interactions().size(), meets.interactions()::toString);
        return new Read(meets.interactions().getFirst(), axes);
    }

    private static long combinations(Interaction group, MeasuredInput.MeasuredAxes axes) {
        InteractionCells.Offered offered = InteractionCells.of(List.of(group), axes,
                Budgets.generation().cellsPerGroup());
        return offered.groups().stream().mapToLong(GenerationFixtures::combinationsOf).sum();
    }

    /** The ways of the first factor with one more that takes two cases of {@code k} at once. */
    private static Interaction withAnImpossibleWay(Interaction group) {
        Factor first = group.factors().getFirst();
        List<Decision> two = new ArrayList<>(first.outcomes().get(0).holds());
        two.addAll(first.outcomes().get(1).holds());
        List<Outcome> ways = new ArrayList<>(first.outcomes());
        ways.add(new Outcome(two));
        List<Factor> factors = new ArrayList<>(group.factors());
        factors.set(0, new Factor(ways));
        return new Interaction(group.reach(), group.reachStated(), factors);
    }

    @Test
    void aWayNoValueTakesLeavesTheCombinationsOfTheWaysThatSomeValueDoes() {
        Read read = read();
        long before = combinations(read.group(), read.axes());
        assertEquals(6L, before, "three cases of one value and two of the other");

        assertEquals(before, combinations(withAnImpossibleWay(read.group()), read.axes()),
                "the way two cases at once is no combination, and the others are all still owed");
    }

    @Test
    void aFactorWithNoWayAnyValueTakesLeavesNoGroup() {
        Read read = read();
        Factor first = read.group().factors().getFirst();
        List<Decision> two = new ArrayList<>(first.outcomes().get(0).holds());
        two.addAll(first.outcomes().get(1).holds());
        List<Factor> factors = new ArrayList<>(read.group().factors());
        factors.set(0, new Factor(List.of(new Outcome(two))));
        Interaction none = new Interaction(read.group().reach(), read.group().reachStated(),
                factors);

        assertTrue(InteractionCells.of(List.of(none), read.axes(),
                Budgets.generation().cellsPerGroup()).groups().isEmpty());
    }
}
