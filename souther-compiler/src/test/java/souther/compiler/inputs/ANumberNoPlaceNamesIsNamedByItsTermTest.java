package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A number that a place and a kind of number do not tell apart from others is named by the term
 * itself, so two such numbers of one place are two numbers to everything that relates them.
 *
 * <p>Held where the naming shows: a number fixed is the number it was fixed at, and fixing one
 * says nothing of another; the difference of two is no number the rules pin. Named by their place,
 * the two would be one atom — the second fixed with the first, and their difference nought.
 */
class ANumberNoPlaceNamesIsNamedByItsTermTest {

    private static final Count FIVE = new Count(BigDecimal.valueOf(5));

    private static final NumericDomain.Bounds AT_FIVE = new NumericDomain.Bounds(
            Endpoint.inclusive(FIVE), Endpoint.inclusive(FIVE));

    /** The totals of {@code amount + 1} and {@code amount + 2} under one key of one list. */
    @Test
    void totalsOfTwoComputationsUnderOneKeyAreTwoNumbers() {
        Quantities read = quantities("""
                module example.ledger

                data Posting = { account: String, amount: Int }

                data Taken

                behavior take : (ps: List<Posting>) -> Taken
                """);
        assertApart(read, totalOf(1), totalOf(2));
    }

    /** The sums of two containers held in every node of one tree. */
    @Test
    void sumsOfTwoContainersInEveryNodeOfATreeAreTwoNumbers() {
        String source = """
                module example.tree

                data Node = { xs: List<Int>, ys: List<Int>, kids: List<Node> }

                data Taken

                behavior take : (n: Node) -> Taken
                """;
        RuleReadingSource rules = rules(source);
        assertApart(quantities(source), sumBelow("xs", rules), sumBelow("ys", rules));
    }

    private static void assertApart(Quantities read, NumericTerm one, NumericTerm other) {
        assertNotEquals(one, other, "the two are two terms to begin with");
        assertEquals(AT_FIVE, read.given(one, FIVE).runsBetween(one),
                () -> "fixing " + one + " fixes it");
        assertEquals(read.runsBetween(other), read.given(one, FIVE).runsBetween(other),
                () -> "fixing " + one + " says nothing of " + other);
        assertNotEquals(new NumericDomain.Bounds(Endpoint.inclusive(new Count(BigDecimal.ZERO)),
                        Endpoint.inclusive(new Count(BigDecimal.ZERO))),
                read.runsBetween(LinearForm.difference(one, other)),
                () -> one + " less " + other + " is no number the rules pin at nought");
        assertNull(one.atItsPlace(), () -> one + " is told apart by no place");
    }

    private static NumericTerm totalOf(int added) {
        return NumericTerm.GatheredUnderItsKey.of(TermPath.of("ps").element(),
                new ElementKey.At(ElementProjection.ofFields(List.of("account"))),
                new ElementValue.Affine(new LinearForm<>(ExactRatio.of(added),
                        Map.of(ElementProjection.ofFields(List.of("amount")), ExactRatio.ONE))),
                Type.Prim.INT, NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, null);
    }

    private static NumericTerm sumBelow(String container, RuleReadingSource rules) {
        return NumericTerm.TakenOver.of(ValueName.Stdlib.operation("List", "sum"),
                RunSource.overTheNodesBelow(TermPath.of("n"), List.of("kids"),
                        List.of(container)),
                Type.Prim.INT, rules.inners(), rules.symbols());
    }

    private static RuleReadingSource rules(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        return RuleReadings.of(compilation, compilation.modules().get(0));
    }

    private static Quantities quantities(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES);
        return InputDomain.of(sigs.get("take"), reading,
                        TypeCardinality.Counts.workedOutIn(reading),
                        souther.compiler.carrier.Membership.none())
                .quantities(rules);
    }
}
