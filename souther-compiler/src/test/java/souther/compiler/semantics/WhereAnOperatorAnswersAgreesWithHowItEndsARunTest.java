package souther.compiler.semantics;

import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSet;
import souther.compiler.abort.AbortSites;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Where an operator answers and what it may end a run for are two answers about one operator, and
 * they agree.
 *
 * <p>{@link AbortSites} says which reasons a run may stop for at an operator and
 * {@link WhereAnOperatorAnswers} says on which operands it does not. An operator answering
 * everywhere is one that ends no run, and one answering on a region ends a run for the reason the
 * region is about: a whole number past what an {@code Int} holds is a form with no place, and a
 * divisor of nought is a division by zero. Held over every operator and every type the checker
 * admits it at, so an operator or a type taught to one of the two and not the other is a failure
 * here and not a disagreement a reader finds.
 */
class WhereAnOperatorAnswersAgreesWithHowItEndsARunTest {

    private static final SourcePos NOWHERE = new SourcePos(0, 0);

    private static int names;

    @Test
    void anOperatorEndsARunForWhatItsRegionLeavesOut() {
        List<String> disagree = new ArrayList<>();
        for (Case each : cases()) {
            Core.Binary binary = new Core.Binary(each.op(), value(each.left()), value(each.right()),
                    Core.BinaryReading.AS_THEY_STAND, ConstructOccurrence.unwritten(),
                    each.answer(), NOWHERE);
            WhereAnOperatorAnswers where = WhereAnOperatorAnswers.ofAnOperator(each.op(),
                    each.answer(), List.of(each.left(), each.right()));
            if (!agree(where, AbortSites.ofAnOperator(binary))) {
                disagree.add(each + ": " + where + " beside " + AbortSites.ofAnOperator(binary));
            }
        }
        for (Type answer : List.of(Type.INT, Type.DECIMAL, Type.RATIONAL)) {
            WhereAnOperatorAnswers where = WhereAnOperatorAnswers.ofANegation(answer);
            AbortSet ends = AbortSites.ofANegation(new Core.Neg(value(answer), answer, NOWHERE));
            if (!agree(where, ends)) {
                disagree.add("negation of " + Type.show(answer) + ": " + where + " beside " + ends);
            }
        }
        assertEquals(List.of(), disagree);
    }

    /** Whether a run outside {@code where} ends for {@code ends} and for nothing else; a region
     *  nothing here says is one some run is outside of, for a reason of its own. */
    private static boolean agree(WhereAnOperatorAnswers where, AbortSet ends) {
        return switch (where) {
            case WhereAnOperatorAnswers.Everywhere _ -> ends.equals(AbortSet.NONE);
            case WhereAnOperatorAnswers.WhereItsExactValueIsHeld _ ->
                    ends.equals(AbortSet.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE));
            case WhereAnOperatorAnswers.WhereTheDivisorIsNotNought _ ->
                    ends.equals(AbortSet.of(AbortKind.DIVISION_BY_ZERO));
            case WhereAnOperatorAnswers.NotStated _ -> !ends.isEmpty();
        };
    }

    /** Every operator at every type the checker admits it at. */
    private static List<Case> cases() {
        List<Case> out = new ArrayList<>();
        for (Type number : List.of(Type.INT, Type.DECIMAL, Type.RATIONAL)) {
            for (BinOp op : List.of(BinOp.ADD, BinOp.SUB, BinOp.MUL)) {
                out.add(new Case(op, number, number, number));
            }
            for (BinOp op : List.of(BinOp.EQ, BinOp.NE, BinOp.LT, BinOp.LE, BinOp.GT, BinOp.GE)) {
                out.add(new Case(op, Type.BOOL, number, number));
            }
            out.add(new Case(BinOp.DIV, Type.RATIONAL, number, number));
        }
        out.add(new Case(BinOp.AND, Type.BOOL, Type.BOOL, Type.BOOL));
        out.add(new Case(BinOp.OR, Type.BOOL, Type.BOOL, Type.BOOL));
        out.add(new Case(BinOp.CONCAT, Type.STRING, Type.STRING, Type.STRING));
        return out;
    }

    /** A name of a value of {@code type}, which is all an operator's reading asks of an operand. */
    private static Core value(Type type) {
        int at = names++;
        return new Core.Read("v" + at, new BindingId(new BindingOwner.OfValue("m", "f"), at), type,
                NOWHERE);
    }

    private record Case(BinOp op, Type answer, Type left, Type right) {}
}
