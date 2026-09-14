package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.DeclaredSig;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.check.RuleReadings;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A combination is one thing to ask for, whichever way round its two classes were written down.
 *
 * <p>What tells a combination from every other is a set: it is a pair of classes and not an order
 * of them. A search walks positions in an order, so somewhere between the two a canonical order has
 * to be chosen — and the one place that happens is {@link Generator.Pins#of}, by the position's
 * number.
 *
 * <p><b>Held over the pins and not only over the identity.</b> Two identities built from the same
 * two classes are equal for free, because a set is. What that says nothing about is the search: a
 * walk that took the classes in the order the set happened to iterate would look in two different
 * places for one requirement, and offer whichever row it reached first.
 */
class APairIsSearchedOneWayRoundHoweverItsClassesAreStoredTest {

    private static final String MODEL = """
            module example.order

            data Domestic
            data Overseas
            data Kind = Domestic | Overseas

            data Amount = Int
                invariant value >= 0

            data Request = { kind: Kind, cost: Amount }
            data Submitted = { cost: Amount }
            data Waiting = { cost: Amount }

            behavior submit : (request: Request) -> Submitted | Waiting
                constructs Submitted, Waiting

            let submit (request) = match request.kind with
                | Domestic -> {
                    guard request.cost.value <= 100 else Waiting { cost = request.cost }
                    Submitted { cost = request.cost }
                }
                | Overseas -> Submitted { cost = request.cost }
            """;

    /** The pins of one combination are the same list whichever order its classes arrive in. */
    @Test
    void thePinsAreTheSameListWhicheverOrderTheClassesArriveIn() {
        MeasuredInput.MeasuredAxes axes = axes();
        Axis one = axes.axes().get(0);
        Axis other = axes.axes().get(1);

        Map<Integer, Integer> ascending = new LinkedHashMap<>();
        ascending.put(0, 0);
        ascending.put(1, 1);
        Map<Integer, Integer> descending = new LinkedHashMap<>();
        descending.put(1, 1);
        descending.put(0, 0);

        assertEquals(Generator.Pins.of(axes, ascending).at(),
                Generator.Pins.of(axes, descending).at(),
                () -> "one combination of " + one.id() + " and " + other.id()
                        + " is searched one way round");
    }

    /** And the identity is the same thing, which is what makes the two orders one requirement. */
    @Test
    void theIdentityIsTheSameCombinationEitherWayRound() {
        MeasuredInput.MeasuredAxes axes = axes();
        ClassOfAPosition one =
                new ClassOfAPosition(axes.axes().get(0).id(), axes.axes().get(0).classes().getFirst().id());
        ClassOfAPosition other =
                new ClassOfAPosition(axes.axes().get(1).id(), axes.axes().get(1).classes().getFirst().id());

        Set<ClassOfAPosition> ascending = new LinkedHashSet<>();
        ascending.add(one);
        ascending.add(other);
        Set<ClassOfAPosition> descending = new LinkedHashSet<>();
        descending.add(other);
        descending.add(one);

        assertEquals(new ObligationIdentity.OfAFallbackPairCell("submit", ascending),
                new ObligationIdentity.OfAFallbackPairCell("submit", descending));
    }

    /**
     * The positions this behavior is measured at, read the way a measurement reads them.
     *
     * <p>Built here rather than asked of the account: what this file is about is the order a
     * search settles two positions in, and that is a question about the axes alone.
     */
    private static MeasuredInput.MeasuredAxes axes() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get("submit");
        CoverageSites.Plan plan = checked.plan();
        InputDomain read = InputDomain.of(sigs.get("submit"), rules,
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
        Partitions.Partitioning partitioning = Partitions.withThresholds(
                Partitions.of("submit", read, rules,
                        souther.compiler.query.ReadAs.THE_COMPILATION_DOES),
                read.quantities(rules),
                GuardThresholds.of("submit", checked.analysisBodies().get("submit"), body, plan,
                        compilation.db()
                                .ask(new souther.compiler.query.Adequacy.Inputs(module)).value()
                                .get("submit"),
                        rules).thresholds(),
                RuleReadingContext.unshared(rules,
                        souther.compiler.query.ReadAs.THE_COMPILATION_DOES),
                souther.compiler.values.Allowance.of(
                        souther.compiler.regex.PatternPlan.Budget.OF_BEHAVIOR_DISTINCTIONS));
        return MeasuredInput.of("submit", read.reading(rules), partitioning).axes();
    }
}
