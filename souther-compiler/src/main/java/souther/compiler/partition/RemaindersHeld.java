package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.WholeNumberRuns;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The statements of remainders a way has taken in, each held to what it leaves of the remainder
 * of its form unmoved.
 *
 * <p>A floor remainder of a form moved by a whole number {@code c} is the remainder of the form
 * moved round the divisor: {@code floorMod(f + c, m)} is {@code r} exactly where
 * {@code floorMod(f, m)} is {@code floorMod(r - c, m)}, for any {@code f}. So statements of one
 * form by one divisor, moved by whatever numbers, are statements of one remainder, and what they
 * leave of it is where each of them holds at once.
 *
 * <p>Only what that shows is held. A form weighed otherwise, or divided by another number, is
 * another remainder, and nothing is said of the two together. A statement of a form with a weight
 * or a move that is not whole, or of a number inside a container — which may be of another
 * element each time — is not taken in. None of those is shown to leave anything, and leaving them
 * out proves nothing about the way.
 */
record RemaindersHeld(Map<Remainder, Left> held) {

    static final RemaindersHeld NONE = new RemaindersHeld(Map.of());

    RemaindersHeld {
        held = Map.copyOf(held);
    }

    /** A remainder of a form unmoved, by a divisor. */
    record Remainder(LinearForm<NumericTerm> form, BigInteger divisor) {}

    /** What the statements of a remainder leave of it, and the statements. */
    record Left(WholeNumberRuns remainders, List<RowDemand.OnARemainder> statements) {

        Left {
            statements = List.copyOf(statements);
        }
    }

    /** What taking a statement in came to. */
    sealed interface Taken {

        /** The statements are held together; this is what they leave. */
        record Held(RemaindersHeld remainders) implements Taken {}

        /** The statements of the one remainder, the last of them the one taken in, leave none of
         *  it. */
        record NoneLeft(List<RowDemand.OnARemainder> statements) implements Taken {}
    }

    /** These with {@code added} taken in, or the statements of its remainder where they leave
     *  none of it. */
    Taken taking(RowDemand.OnARemainder added) {
        LinearForm<NumericTerm> dividend = added.dividend();
        if (!dividend.constant().isWhole()
                || !(dividend.constant().floor() instanceof ExactAnswer.Held<BigInteger>(
                        BigInteger moved))) {
            return new Taken.Held(this);
        }
        for (Map.Entry<NumericTerm, ExactRatio> each : dividend.coefs().entrySet()) {
            if (!each.getValue().isWhole() || each.getKey().subjectPath().insideAContainer()) {
                return new Taken.Held(this);
            }
        }
        BigInteger divisor = added.remainder().divisor();
        Remainder of = new Remainder(new LinearForm<>(ExactRatio.ZERO, dividend.coefs()), divisor);
        WholeNumberRuns leaves = Standing.OfARemainder.turnedBack(added.leaves(), moved, divisor);
        Left before = held.get(of);
        List<RowDemand.OnARemainder> statements = new ArrayList<>();
        if (before != null) {
            statements.addAll(before.statements());
            leaves = leaves.and(before.remainders());
        }
        statements.add(added);
        if (leaves.isNone()) {
            return new Taken.NoneLeft(statements);
        }
        Map<Remainder, Left> out = new LinkedHashMap<>(held);
        out.put(of, new Left(leaves, statements));
        return new Taken.Held(new RemaindersHeld(out));
    }
}
