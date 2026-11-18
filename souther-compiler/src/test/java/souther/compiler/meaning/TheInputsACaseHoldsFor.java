package souther.compiler.meaning;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * Whether two inputs, one holding a line and one failing it, meet one case, worked out by
 * evaluating each condition at the input's numbers and set and never by what a proof reads of it.
 *
 * <p>What the proof that no case crosses ({@link NoCaseCrosses}) is held to, by every pair of the
 * inputs a test hands it.
 */
final class TheInputsACaseHoldsFor {

    private TheInputsACaseHoldsFor() {
    }

    static final Quantity X = new DecisionAtom.OfTheInput(
            new NumericTerm.ValueOf(TermPath.of("x")));
    static final Quantity Y = new DecisionAtom.OfTheInput(
            new NumericTerm.ValueOf(TermPath.of("y")));

    static final DecisionSubject.AnInput HOLIDAYS =
            new DecisionSubject.AnInput(TermPath.of("holidays"));
    static final Quantity MEMBER = new DecisionAtom.OfTheInput(
            new NumericTerm.ValueOf(TermPath.of("holidays").element()));

    static Proposition.Compared relation(Map<Quantity, Integer> coefs, int constant,
                                                 Rel rel, boolean holds) {
        Map<Quantity, ExactRatio> by = new LinkedHashMap<>();
        coefs.forEach((quantity, coef) -> by.put(quantity, ExactRatio.of(coef)));
        return new Proposition.Compared(new Relation.Affine(
                new LinearForm<>(ExactRatio.of(constant), by), rel), holds);
    }

    static Quantity remainder(Quantity of, int by, int divisor) {
        return new Quantity.RemainderOfADividend(ValueName.Stdlib.operation("Int", "floorMod"),
                new LinearForm<>(ExactRatio.of(by), Map.of(of, ExactRatio.ONE)),
                BigInteger.valueOf(divisor));
    }

    /** What an input is: two numbers and a set. */
    record Input(int x, int y, Set<Integer> holidays) {}

    /** The inputs whose numbers are each {@code low} to {@code high}, with every set of the numbers
     *  one to three where {@code withSets} and none otherwise. */
    static List<Input> inputs(int low, int high, boolean withSets) {
        List<Input> out = new ArrayList<>();
        for (int x = low; x <= high; x++) {
            for (int y = low; y <= high; y++) {
                for (int mask = 0; mask < (withSets ? 8 : 1); mask++) {
                    Set<Integer> held = new TreeSet<>();
                    for (int bit = 0; bit < 3; bit++) {
                        if ((mask & (1 << bit)) != 0) {
                            held.add(bit + 1);
                        }
                    }
                    out.add(new Input(x, y, held));
                }
            }
        }
        return out;
    }

    // ---- what a condition holds of an input, worked out here and not by the proof ----

    static long value(Quantity quantity, Input in, Integer element) {
        if (quantity.equals(X)) {
            return in.x();
        }
        if (quantity.equals(Y)) {
            return in.y();
        }
        if (quantity.equals(MEMBER)) {
            return element;
        }
        Quantity.RemainderOfADividend remainder = (Quantity.RemainderOfADividend) quantity;
        long dividend = form(remainder.dividend(), in, element);
        return Math.floorMod(dividend, remainder.divisor().longValueExact());
    }

    static long form(LinearForm<Quantity> form, Input in, Integer element) {
        long sum = whole(form.constant());
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            sum += whole(each.getValue()) * value(each.getKey(), in, element);
        }
        return sum;
    }

    static long whole(ExactRatio ratio) {
        return ((ExactAnswer.Held<BigInteger>) ratio.floor()).value().longValueExact();
    }

    static boolean holds(Proposition p, Input in, Integer element) {
        return switch (p) {
            case Proposition.Compared c -> {
                Relation.Affine affine = (Relation.Affine) c.relation();
                long form = form(affine.form(), in, element);
                boolean read = switch (affine.proposition()) {
                    case GE -> form >= 0;
                    case GT -> form > 0;
                    case LE -> form <= 0;
                    case LT -> form < 0;
                    case EQ -> form == 0;
                    case NE -> form != 0;
                };
                yield c.holds() == read;
            }
            case Proposition.All all -> all.parts().stream().allMatch(part -> holds(part, in, element));
            case Proposition.Any any -> any.parts().stream().anyMatch(part -> holds(part, in, element));
            case Proposition.Some some -> {
                boolean found = false;
                for (int each : in.holidays()) {
                    found |= holds(some.ofTheElement(), in, each);
                }
                yield some.holds() == found;
            }
            default -> throw new IllegalArgumentException(p.toString());
        };
    }

    /** Whether some case of {@code cases} holds for both inputs: each of them chosen through
     *  alone where it is an alternative, every factor of one where it is held together. */
    static boolean someCaseHoldsFor(DecidingCase.Cases cases, Input one, Input other,
                                            Map<Object, Boolean> memo) {
        Boolean known = memo.get(cases);
        if (known != null) {
            return known;
        }
        boolean out = switch (cases) {
            case DecidingCase.Cases.One c -> holds(c.condition(), one, null)
                    && holds(c.condition(), other, null);
            case DecidingCase.Cases.EachOf each -> each.alternatives().stream()
                    .anyMatch(a -> someCaseHoldsFor(a, one, other, memo));
            case DecidingCase.Cases.Together together -> together.factors().stream()
                    .allMatch(a -> someCaseHoldsFor(a, one, other, memo));
            case DecidingCase.Cases.NotTakenApart _ -> true;
        };
        memo.put(cases, out);
        return out;
    }

    /** Whether two inputs, one holding {@code line} and one failing it, meet one case. */
    static boolean someCaseCrosses(Proposition.Compared line, DecidingCase.Cases cases,
                                           List<Input> inputs) {
        for (Input holding : inputs) {
            if (!holds(line, holding, null)) {
                continue;
            }
            for (Input failing : inputs) {
                if (holds(line, failing, null)) {
                    continue;
                }
                if (someCaseHoldsFor(cases, holding, failing, new IdentityHashMap<>())) {
                    return true;
                }
            }
        }
        return false;
    }
}
