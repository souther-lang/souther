package souther.compiler.values;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a choice leaves does not turn on how its alternatives were bracketed or ordered.
 *
 * <p>{@code ||} is one connective. Three alternatives are three alternatives, and a reading that
 * answers one thing about {@code (a || b) || c} and another about {@code a || (b || c)} is reading
 * the tree the parser built rather than the rule the author wrote. The same goes for the order they
 * are written in.
 *
 * <p>Held over every triple of a small set of readings rather than over an example, because this is
 * the property the whole of {@link AdmissibleValues#guaranteedAt} exists to keep and the way to
 * lose it is to answer from something that only one bracketing has in hand. What is compared is
 * what a caller reads: which values a position holds, and whether this can speak for it. The reason
 * a position is left standing is not compared — a rule that named the position outranks a branch
 * that widened it, so which of two rules is nearer does turn on which is written first. Beside
 * those, whether the reading admits anything and whether its promise is one about whole values,
 * since a conjunction written after the choice reads both and would answer differently past it.
 *
 * <p>One composer for the whole of a test, since a reading is one answer being built. Every set
 * here is finitely many values written out, so nothing is ever built and no allowance is spent —
 * what the composer is doing is being the one place a composition happens.
 */
class AChoiceIsOneConnectiveAndNotATreeTest {

    private static final List<String> POSITIONS = List.of("value", "other", "neither");

    /**
     * What every choice here is told its unread alternative left open.
     *
     * <p>The same at every bracketing, which is what the property needs: whether a choice opened a
     * position is settled where the alternatives an author wrote are in hand, so a bracketing
     * cannot change it and this test may not let one. What is held is that everything the join does
     * with it is associative and commutative too.
     */
    private static final Set<String> OPENED = Set.of("value", "other");
    private static final Value A = Value.text("A");
    private static final Value B = Value.text("B");

    private final Allowance<String> sets = AsACompilationAllows.forAdmittedValues();

    private Map<String, AdmissibleValues<String>> readings() {
        Map<String, AdmissibleValues<String>> out = new LinkedHashMap<>();
        out.put("top", AdmissibleValues.top());
        out.put("value == A", AdmissibleValues.at("value", ValueSet.just(A)));
        out.put("value == B", AdmissibleValues.at("value", ValueSet.just(B)));
        out.put("value /= A", AdmissibleValues.at("value", ValueSet.allBut(A)));
        out.put("other == A", AdmissibleValues.at("other", ValueSet.just(A)));
        out.put("value == A && other == A", AdmissibleValues.at("value", ValueSet.just(A))
                .meet(AdmissibleValues.at("other", ValueSet.just(A)), sets));
        out.put("value == B && other == B", AdmissibleValues.at("value", ValueSet.just(B))
                .meet(AdmissibleValues.at("other", ValueSet.just(B)), sets));
        out.put("unread about value",
                AdmissibleValues.unreadable(Set.of("value"), UnreadReason.FORM_NOT_READ));
        out.put("unread about nothing",
                AdmissibleValues.unreadable(Set.of(), UnreadReason.FORM_NOT_READ));
        out.put("unread about both", AdmissibleValues.unreadable(Set.of("value", "other"),
                UnreadReason.RELATES_TWO_POSITIONS));
        out.put("two rules leaving nothing", AdmissibleValues.at("value", ValueSet.just(A))
                .meet(AdmissibleValues.at("value", ValueSet.just(B)), sets));
        out.put("shown impossible from outside",
                AdmissibleValues.at("value", ValueSet.just(A)).leavingNothing());
        return out;
    }

    /**
     * What a caller reads off a state, at every position, as one comparable value.
     *
     * <p>The sets themselves and not what they print. {@link ValueSet} keeps its values in the
     * order the model wrote them, so two readings of one choice hold the same set written two ways
     * — which is a set and is equal, and is two strings and is not.
     */
    private static List<Object> answers(AdmissibleValues<String> state) {
        List<Object> out = new ArrayList<>();
        POSITIONS.forEach(atom -> {
            out.add(state.at(atom));
            out.add(state.speaksFor(atom));
            out.add(state.guaranteedAt(atom));
            // And whether the reading can promise this position's answer, which is asked of the
            // position for the reason the values are.
            out.add(state.projectionExactAt(atom));
        });
        // Neither of these is read by a caller and a conjunction reads both, so a bracketing that
        // told a conjunction something different about its sides would answer differently past it
        // and nowhere before.
        out.add(state.guaranteedTogether());
        out.add(state.isBottom());
        // And what the reading may promise about its own exactness, for the same reason and one
        // more: these are read where a report decides whether the values it prints are what the
        // model leaves, so a bracketing that changed them would change what a document says about
        // a model whose author wrote one clause.
        out.add(state.relationExact());
        return out;
    }

    /** Three alternatives leave what they leave, however they are bracketed. */
    @Test
    void threeAlternativesLeaveTheSameHoweverTheyAreBracketed() {
        Map<String, AdmissibleValues<String>> readings = readings();
        readings.forEach((leftName, left) -> readings.forEach((middleName, middle) ->
                readings.forEach((rightName, right) -> assertEquals(
                        answers(left.join(middle, sets, OPENED).join(right, sets, OPENED)),
                        answers(left.join(middle.join(right, sets, OPENED), sets, OPENED)),
                        () -> "(" + leftName + " || " + middleName + ") || " + rightName
                                + "   against   " + leftName + " || (" + middleName + " || "
                                + rightName + ")"))));
    }

    /** And however they are ordered. */
    @Test
    void twoAlternativesLeaveTheSameHoweverTheyAreOrdered() {
        Map<String, AdmissibleValues<String>> readings = readings();
        readings.forEach((leftName, left) -> readings.forEach((rightName, right) ->
                assertEquals(answers(left.join(right, sets, OPENED)),
                        answers(right.join(left, sets, OPENED)),
                        () -> leftName + " || " + rightName + "   against   "
                                + rightName + " || " + leftName)));
    }

    /** And a conjunction beside them reads the same, wherever the brackets of the choice fell. */
    @Test
    void aConjunctionBesideThemReadsTheSameEitherWay() {
        Map<String, AdmissibleValues<String>> readings = readings();
        AdmissibleValues<String> beside = AdmissibleValues.at("other", ValueSet.allBut(B));
        readings.forEach((leftName, left) -> readings.forEach((middleName, middle) ->
                readings.forEach((rightName, right) -> assertEquals(
                        answers(left.join(middle, sets, OPENED).join(right, sets, OPENED)
                                .meet(beside, sets)),
                        answers(left.join(middle.join(right, sets, OPENED), sets, OPENED)
                                .meet(beside, sets)),
                        () -> "(" + leftName + " || " + middleName + ") || " + rightName
                                + "   met with other /= B, against the other bracketing"))));
    }

    /**
     * And so does a further alternative written after that conjunction.
     *
     * <p>The one that reaches furthest. What a conjunction may promise is settled by what its sides
     * promise, and what a choice after it discharges is settled by that promise — so a bracketing
     * that told the conjunction something different about its sides comes out here and nowhere
     * earlier.
     */
    @Test
    void andAFurtherAlternativeAfterThatConjunctionReadsTheSame() {
        Map<String, AdmissibleValues<String>> readings = readings();
        AdmissibleValues<String> beside = AdmissibleValues.at("other", ValueSet.allBut(B));
        AdmissibleValues<String> after =
                AdmissibleValues.unreadable(Set.of("value"), UnreadReason.FORM_NOT_READ);
        readings.forEach((leftName, left) -> readings.forEach((middleName, middle) ->
                readings.forEach((rightName, right) -> assertEquals(
                        answers(left.join(middle, sets, OPENED).join(right, sets, OPENED)
                                .meet(beside, sets).join(after, sets, OPENED)),
                        answers(left.join(middle.join(right, sets, OPENED), sets, OPENED)
                                .meet(beside, sets).join(after, sets, OPENED)),
                        () -> "(" + leftName + " || " + middleName + ") || " + rightName
                                + "   met with other /= B and joined with an unread rule about"
                                + " value, against the other bracketing"))));
    }
}
