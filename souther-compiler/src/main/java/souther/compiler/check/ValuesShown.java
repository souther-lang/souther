package souther.compiler.check;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.math.BigInteger;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * How many values of a type that differ are shown to exist, from one up — or none where no value
 * is shown, which is not that there is none.
 *
 * <p>The side of {@link Cardinality} that is a lower bound. That one counts at most and carries a
 * proof of none; nothing in it says a value is there, and an answer of "not shown to be none" is
 * the widest it gives. This is the answer a reader needs to say that a collection of some size is
 * a value some row holds, and it is as cautious the other way: a type whose rules this does not
 * read as exactly where its numbers lie is shown no value, and a type written in terms of itself
 * is shown none either, so a count here is never more than the type has.
 *
 * <p>Asked of what a type <em>is</em> ({@link Shape}) and of the rules its names carry
 * ({@link DeclaredClauses}), and of nothing else: a type is read once by {@link TypeView}, and a
 * second walk over {@link Type} would answer afresh what a name denotes. A value of a declared type
 * is built of the values of its parts, and so a type carrying no rule is as many as its parts
 * make; one carrying a rule is as many as the rule is read to leave, which is a run of numbers
 * where the rule is nothing but ends on a whole number ({@link DeclaredBounds#wholeRunOf}).
 */
public final class ValuesShown {

    private ValuesShown() {
    }

    /**
     * At least this many values of {@code type} that differ are shown to exist, ending at the most
     * a collection holds — a count past it is no more to anything asked of a collection.
     */
    public static long of(Type type, RuleReadingContext reading) {
        return of(type, reading, new HashSet<>());
    }

    private static long of(Type type, RuleReadingContext reading, Set<TypeSymbol> inside) {
        RuleReadingSource source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        for (TypeSymbol wears : view.wrappers()) {
            if (!inside.add(wears)) {
                return 0;
            }
        }
        long unwrapped = ofShape(view, reading, inside);
        return carriesNoRule(view.wrappers(), source) ? unwrapped
                : Math.min(unwrapped, ofTheRules(view, reading));
    }

    private static long ofShape(TypeView view, RuleReadingContext reading,
                                Set<TypeSymbol> inside) {
        RuleReadingSource source = reading.source();
        return switch (view.shape()) {
            case Shape.Scalar scalar -> switch (scalar.prim()) {
                case INT, STRING, DECIMAL, RATIONAL -> most();
                case BOOL, DATE, TIME, DATETIME, INSTANT -> 2L;
            };
            case Shape.Unit unit -> carriesNoRule(List.of(unit.name()), source) ? 1L : 0L;
            case Shape.Product product -> {
                if (!carriesNoRule(List.of(product.name()), source)
                        || !inside.add(product.name())) {
                    yield 0L;
                }
                long count = 1;
                for (Type field : product.fields().values()) {
                    count = times(count, of(field, reading, new HashSet<>(inside)));
                }
                yield count;
            }
            case Shape.Sum sum -> {
                if (!(sum.common() instanceof Shape.CommonProduct.None)
                        || !carriesNoRule(List.of(sum.name()), source)
                        || !inside.add(sum.name())) {
                    yield 0L;
                }
                long count = 0;
                for (TypeSymbol leaf : sum.reaches().cases()) {
                    count = Math.min(most(), count + of(new Type.Ref(leaf), reading,
                            new HashSet<>(inside)));
                }
                yield count;
            }
            case Shape.Optional option ->
                    Math.min(most(), 1 + of(option.element(), reading, new HashSet<>(inside)));
            case Shape.Sequence sequence -> switch (sequence.kind()) {
                case LIST -> of(sequence.element(), reading, new HashSet<>(inside)) >= 1
                        ? most() : 1L;
                case SET -> powerOfTwo(of(sequence.element(), reading, new HashSet<>(inside)));
            };
            case Shape.Mapping map -> of(map.key(), reading, new HashSet<>(inside)) >= 1
                    && of(map.value(), reading, new HashSet<>(inside)) >= 1 ? 2L : 1L;
            case Shape.Tuple tuple -> {
                long count = 1;
                for (Type each : tuple.elements()) {
                    count = times(count, of(each, reading, new HashSet<>(inside)));
                }
                yield count;
            }
            // A union nobody named has no declaration to carry a rule, and each member is a name
            // that does.
            case Shape.Cases union -> {
                long count = 0;
                for (TypeSymbol member : union.members()) {
                    count = Math.min(most(), count + of(new Type.Ref(member), reading,
                            new HashSet<>(inside)));
                }
                yield count;
            }
            case Shape.Function _, Shape.Uninhabited _, Shape.Bottom _, Shape.Erroneous _,
                 Shape.Undecided _, Shape.Unresolved _ -> 0L;
        };
    }

    /** Whether every name is shown to carry no rule: none was listed and none was left out. */
    private static boolean carriesNoRule(List<TypeSymbol> names, RuleReadingSource source) {
        return DeclaredClauses.of(names, source).stream().allMatch(
                DeclaredClauses.OnAName::carriesNone);
    }

    /**
     * What the rules of a number written under names leave of it, where they are nothing but ends:
     * the whole numbers between them, or one value where it is not a whole number that is left.
     * Nought where the rules are anything else, which this does not read as leaving a value.
     */
    private static long ofTheRules(TypeView view, RuleReadingContext reading) {
        NumericDomain.Bounds run = DeclaredBounds.wholeRunOf(view, reading);
        if (run == null || !run.holdsAValue()) {
            return 0;
        }
        if (!(view.shape() instanceof Shape.Scalar scalar) || scalar.prim() != Type.Prim.INT) {
            return 1;
        }
        return wholeNumbersIn(run);
    }

    private static long wholeNumbersIn(NumericDomain.Bounds run) {
        Endpoint low = run.min();
        Endpoint high = run.max();
        if (low == null || high == null || !(low.at() instanceof Count from)
                || !(high.at() instanceof Count to)) {
            return most();
        }
        ExactRatio first = low.inclusive() ? from.exactly()
                : from.exactly().plus(ExactRatio.ONE).orNull();
        ExactRatio last = high.inclusive() ? to.exactly()
                : to.exactly().minus(ExactRatio.ONE).orNull();
        ExactRatio held = first == null || last == null ? null
                : last.minus(first).orNull() instanceof ExactRatio span
                        ? span.plus(ExactRatio.ONE).orNull() : null;
        // A count this reads no further than one value is still one value shown.
        if (held == null || !(held.floor() instanceof ExactAnswer.Held<BigInteger>(
                BigInteger whole))) {
            return 1;
        }
        return whole.signum() <= 0 ? 0
                : whole.compareTo(BigInteger.valueOf(most())) >= 0 ? most() : whole.longValue();
    }

    /** {@code count} times {@code by}, ending at the most a collection holds. */
    private static long times(long count, long by) {
        return by == 0 || count == 0 ? 0 : by > most() / count ? most() : count * by;
    }

    /** Two to the {@code power}, ending at the most a collection holds. */
    private static long powerOfTwo(long power) {
        return power >= Long.SIZE - Long.numberOfLeadingZeros(most()) ? most()
                : Math.min(most(), 1L << power);
    }

    private static long most() {
        return EverySizeAContainerHas.mostHeld();
    }
}
