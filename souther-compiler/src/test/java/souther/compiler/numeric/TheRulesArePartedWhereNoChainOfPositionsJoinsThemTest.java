package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * The rules are parted into exactly the pieces no chain of shared positions joins.
 *
 * <p>Held here and not only through what the closure comes to. A parting that joins too little
 * answers wrongly and the theorem test of the product sees it; a parting that joins too much answers
 * rightly — one part closed in one run is the closure — and is seen by nothing that compares
 * answers, while every part it joined needlessly is a closure worked out again for a change in the
 * other. So the parts themselves are what is compared, on rules written so that each way of joining
 * is asked once: a chain through a shared position, a rule that joins two parts already made, and
 * rules that share nothing.
 */
class TheRulesArePartedWhereNoChainOfPositionsJoinsThemTest {

    /** {@code a - b} and then {@code b - c}: one part, through {@code b}, though no rule names both
     *  {@code a} and {@code c}. */
    @Test
    void aChainThroughASharedPositionIsOnePart() {
        AffineConstraint<String> ab = rule("a", "b");
        AffineConstraint<String> bc = rule("b", "c");

        assertEquals(List.of(List.of(ab, bc)), ClosureQuestion.independentRules(List.of(ab, bc)));
    }

    /**
     * Two parts already made, and then a rule naming a position of each: one part, which is the two
     * of them joined and not the later rule joined to one of them.
     */
    @Test
    void aRuleNamingTwoPartsJoinsThemWhole() {
        AffineConstraint<String> ab = rule("a", "b");
        AffineConstraint<String> cd = rule("c", "d");
        AffineConstraint<String> de = rule("d", "e");
        AffineConstraint<String> eb = rule("e", "b");

        assertEquals(List.of(List.of(ab, cd, de, eb)),
                ClosureQuestion.independentRules(List.of(ab, cd, de, eb)));
    }

    /**
     * A rule whose positions were first named by rules already joined to others joins the whole
     * of each of those parts, and not only the rules that first named its positions.
     *
     * <p>{@code s} is first named by the second rule, which is joined to the first; {@code c} by the
     * fourth, which is joined to the third. The last rule joins the two parts through rules neither
     * of which stands for its part. Written both ways round, since which of its positions is taken
     * first is the form's to say.
     */
    @Test
    void aRuleJoiningRulesAlreadyJoinedElsewhereJoinsTheirWholeParts() {
        AffineConstraint<String> p = rule("p");
        AffineConstraint<String> ps = rule("p", "s");
        AffineConstraint<String> q = rule("q");
        AffineConstraint<String> qc = rule("q", "c");
        for (AffineConstraint<String> joining : List.of(rule("s", "c"), rule("c", "s"))) {
            assertEquals(List.of(List.of(p, ps, q, qc, joining)),
                    ClosureQuestion.independentRules(List.of(p, ps, q, qc, joining)),
                    () -> "joined through " + joining);
        }
    }

    /** A sum over three positions joins all three, whichever two of them other rules name. */
    @Test
    void aSumOverThreePositionsJoinsEveryOneOfThem() {
        AffineConstraint<String> sum = rule("a", "b", "c");
        AffineConstraint<String> onTheLast = rule("c", "d");
        AffineConstraint<String> apart = rule("x", "y");

        assertEquals(List.of(List.of(sum, onTheLast), List.of(apart)),
                ClosureQuestion.independentRules(List.of(sum, apart, onTheLast)));
    }

    /**
     * Rules that share nothing stay apart, each part where its first rule is and each rule where it
     * was handed over.
     *
     * <p>The order is what lets a part's closure read its rules as the closure of all of them
     * would, so it is held as well as the grouping.
     */
    @Test
    void rulesThatShareNothingStayApartInTheOrderTheyCame() {
        AffineConstraint<String> xy = rule("x", "y");
        AffineConstraint<String> ab = rule("a", "b");
        AffineConstraint<String> yz = rule("y", "z");
        AffineConstraint<String> onlyC = rule("c");

        assertEquals(List.of(List.of(xy, yz), List.of(ab), List.of(onlyC)),
                ClosureQuestion.independentRules(List.of(xy, ab, yz, onlyC)));
    }

    /** {@code Σ position <= 1} over {@code positions}, weighed by one apiece. */
    private static AffineConstraint<String> rule(String... positions) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        for (String position : positions) {
            coefs.put(position, ExactRatio.ONE);
        }
        AffineConstraint.Read<String> read = AffineConstraint.of(coefs, ExactRatio.ONE.negated(),
                Rel.LE, _ -> Granularity.DISCRETE);
        assertInstanceOf(AffineConstraint.Read.Stated.class, read);
        return ((AffineConstraint.Read.Stated<String>) read).constraint();
    }
}
