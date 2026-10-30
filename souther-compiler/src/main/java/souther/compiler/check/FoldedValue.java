package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.core.Kernel;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * What an expression comes to at compile time, read in whatever environment its names are read in.
 *
 * <p>One walk for every reader that folds. The discharge of a rule and the reading of an input both
 * ask what a value written down comes to — the text a predicate is about, the number a divisor is,
 * whether a condition holds — and each reads names in an environment of its own. Two folds would be
 * a rule checked as stating one text and measured as stating none the first time one of them learned
 * a shape the other did not. So how far a value is followed is {@link ValueStanding}'s, with the
 * reader's own answers to what its names denote ({@link ValueStanding.Names}): a name, a binding's
 * body, a field or element taken off what was written, and a build of a value. What an operator makes
 * of the constants under it is {@link ConstantAlgebra}'s.
 *
 * <p>A name read more than once in one environment is folded once, so a chain of names each read
 * twice costs a fold per link rather than two to the power of its length.
 *
 * @param <E> the environment names are read in
 * @param <N> what answers for it
 */
public final class FoldedValue<E, N extends ValueStanding.Names<E, N>> {

    /** Where a test counts the names this folds rather than finds folded already, and null
     *  everywhere else. What a chain of names costs is not something an answer says. */
    static long[] FOLDED;

    private final N names;
    private final Symbols symbols;

    /** What each name came to, by what it stands for where it is read ({@link
     *  ValueStanding.Names#standingOf}), told apart by identity. */
    private final Map<Object, Map<BindingId, Optional<Object>>> folded;

    private FoldedValue(N names, Symbols symbols,
                        Map<Object, Map<BindingId, Optional<Object>>> folded) {
        this.names = names;
        this.symbols = symbols;
        this.folded = folded;
    }

    /** What {@code e}, read in {@code at} with {@code names}, folds to — or empty where it is not a
     *  compile-time constant. */
    public static <E, N extends ValueStanding.Names<E, N>> Optional<Object> of(
            Core e, E at, N names, Symbols symbols) {
        return new FoldedValue<>(names, symbols, new IdentityHashMap<>()).eval(e, at);
    }

    /**
     * The same, with what each name came to held in {@code kept} from one fold to the next.
     *
     * <p>For a reader that folds many expressions over one set of environments with the same
     * {@code names} — a walk asking what each operator it passes is worked out of — so a name read
     * by each of them is folded once rather than once for each.
     */
    public static <E, N extends ValueStanding.Names<E, N>> Optional<Object> of(
            Core e, E at, N names, Symbols symbols, Kept kept) {
        return new FoldedValue<>(names, symbols, kept.folded).eval(e, at);
    }

    /**
     * What each name came to, held for as long as whoever holds it folds with one reading of the
     * names, and handed to no other: what a name comes to is that reading's answer.
     */
    public static final class Kept {
        private final Map<Object, Map<BindingId, Optional<Object>>> folded =
                new IdentityHashMap<>();
    }

    /** The number a fold came to, as a decimal — or null where it came to none, or to a number
     *  that is not whole or written ({@code ExactRatio} arrives only through the operators, each of
     *  which arithmetic composes). */
    public static BigDecimal number(Optional<Object> folded) {
        return switch (folded.orElse(null)) {
            case Long n -> BigDecimal.valueOf(n);
            case BigDecimal d -> d;
            case null, default -> null;
        };
    }

    private Optional<Object> eval(Core asPlaced, E at) {
        Core e = Core.withoutStanding(asPlaced);
        if (e instanceof Core.Read read) {
            return given(read, at);
        }
        ValueStanding.Standing<E, N> stands = ValueStanding.one(e, at, names);
        Core value = Core.withoutStanding(stands.value());
        if (value != e) {
            return eval(value, stands.at());
        }
        // A constant is the value it is whatever type it stands as.
        return switch (value) {
            case Core.Int i -> Optional.of(i.value());
            case Core.Decimal d -> Optional.of(d.value());
            case Core.Str s -> Optional.of(s.value());
            case Core.Bool b -> Optional.of(b.value());
            case Core.Neg n -> ConstantAlgebra.negate(eval(n.operand(), at).orElse(null));
            case Core.Binary b -> binary(b, at);
            case Core.PreservedCall call -> call(call, at);
            // The arm the condition takes and no other, as a run works it out.
            case Core.If choice -> eval(choice.cond(), at).orElse(null) instanceof Boolean taken
                    ? eval(taken ? choice.then() : choice.els(), at) : Optional.empty();
            case null, default -> Optional.empty();
        };
    }

    /**
     * What the name {@code read} comes to in {@code at}: what the environment says it denotes,
     * folded where that was written — or empty where it denotes nothing one value is.
     */
    private Optional<Object> given(Core.Read read, E at) {
        Map<BindingId, Optional<Object>> here = folded.computeIfAbsent(
                names.standingOf(read, at), _ -> new HashMap<>());
        Optional<Object> already = here.get(read.binding());
        if (already != null) {
            return already;
        }
        long[] counting = FOLDED;
        if (counting != null) {
            counting[0]++;
        }
        // Put before the fold as "not a constant", so a name that reaches itself answers rather
        // than going round.
        here.put(read.binding(), Optional.empty());
        Optional<Object> answer = ValueStanding.named(read, at, names)
                instanceof ValueStanding.Named.One<E, N>(ValueStanding.Standing<E, N> one)
                ? eval(one.value(), one.at()) : Optional.empty();
        here.put(read.binding(), answer);
        return answer;
    }

    private Optional<Object> binary(Core.Binary b, E at) {
        Optional<Object> left = eval(b.left(), at);
        Optional<Object> settled = left.isEmpty() ? Optional.empty()
                : ConstantAlgebra.settledByTheLeft(b.op(), left.get());
        if (settled.isPresent()) {
            return settled;
        }
        Optional<Object> right = eval(b.right(), at);
        if (left.isEmpty() || right.isEmpty()) {
            return Optional.empty();
        }
        return ConstantAlgebra.binary(b.op(), left.get(), right.get());
    }

    /** The furthest from nought a scale is folded at, which no rounding a model writes is past. */
    private static final int MOST_SCALE = 1000;

    /**
     * What a rounding to a step comes to, for an operation the library says rounds: the number
     * taken to the scale, rounded the way the policy written there rounds, and written at it.
     *
     * <p>Which operations round, which of their arguments are the scale, the policy and the number,
     * and what each way of rounding does are the library's to say ({@link ARounding}), asked here as
     * every other reader of a rounding asks. Folded with a way of the compiler's own, a rounding
     * would be one thing where it is discharged and another where its bounds are read.
     */
    private Optional<Object> rounded(Core.PreservedCall call, E at) {
        AnOperationApplied applied = AnOperationApplied.of(call);
        ARounding rounds = applied == null ? null
                : DefaultBoundOperationFacts.get().rounding(applied);
        if (rounds == null) {
            return Optional.empty();
        }
        Object scale = rounds.scale() == null ? Long.valueOf(0)
                : eval(rounds.scale(), at).orElse(null);
        WholeRounding way = rounds.wayOf(Core.withoutStanding(rounds.policy()));
        Object folded = eval(rounds.rounded(), at).orElse(null);
        ExactRatio number = folded == null ? null : ConstantAlgebra.exactly(folded);
        if (!(scale instanceof Long places) || way == null || number == null
                || Math.abs(places) > MOST_SCALE
                || !ARounding.answersAtAScale(BigInteger.valueOf(places))) {
            return Optional.empty();
        }
        ExactRatio ten = ExactRatio.of(BigInteger.TEN.pow((int) Math.abs(places)));
        ExactRatio scaled = (places >= 0 ? number.times(ten) : number.dividedBy(ten)).orNull();
        BigInteger whole = scaled == null ? null : way.of(scaled);
        if (whole == null) {
            return Optional.empty();
        }
        if (call.type() == Type.DECIMAL) {
            return Optional.of(new BigDecimal(whole, (int) (long) places));
        }
        return whole.bitLength() < Long.SIZE ? Optional.of(whole.longValue()) : Optional.empty();
    }

    private Optional<Object> call(Core.PreservedCall call, E at) {
        if (!(call.operation() instanceof ValueName.Stdlib.Operation operation)) {
            return Optional.empty();
        }
        // A denial is kept as the call it is, and what it answers is its law's to say, which is
        // the reading of a clause's own word for it ({@link DischargeRules#denies}).
        if (DischargeRules.denies(operation) && call.args().size() == 1) {
            return eval(call.args().getFirst(), at).orElse(null) instanceof Boolean held
                    ? Optional.of(!held) : Optional.empty();
        }
        Optional<Object> rounding = rounded(call, at);
        if (rounding.isPresent()) {
            return rounding;
        }
        Kernel kernel = symbols.kernelOf(operation);
        if (kernel == null) {
            return Optional.empty();
        }
        // A pattern is not folded to text and read again: the checker read it where it settled the
        // call, and what it means is on the call. Only the subject is folded, which is the last
        // argument (spec §pipe).
        if (call.settled() instanceof Core.KernelFact.StringMatches settled) {
            return eval(call.args().getLast(), at).orElse(null) instanceof String subject
                    ? ConstantAlgebra.matching(settled.meaning(), subject) : Optional.empty();
        }
        List<Object> args = new ArrayList<>();
        for (Core arg : call.args()) {
            Object folds = eval(arg, at).orElse(null);
            if (folds == null) {
                return Optional.empty();
            }
            args.add(folds);
        }
        return ConstantAlgebra.computed(kernel, args);
    }
}
