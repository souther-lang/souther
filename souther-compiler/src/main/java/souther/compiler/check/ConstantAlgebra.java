package souther.compiler.check;

import souther.compiler.core.Kernel;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BinOp;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;
import souther.compiler.regex.PatternMeaning;
import souther.compiler.regex.PatternParser;
import souther.compiler.regex.PatternPlan;
import souther.compiler.regex.PatternRead;
import souther.compiler.regex.Recognizer;
import souther.unicode.Normalization;
import souther.unicode.ScalarValues;

/**
 * What an expression comes to where the values under it are already known.
 *
 * <p>The arithmetic of folding and nothing else: given the constants an operator's operands came
 * to, what the operator makes of them. How those operands were reached — which tree was walked,
 * which names were in force, which bindings were followed — is the walk's, and there is more than
 * one walk. A body is read as {@link souther.compiler.ast.Hir} where it is checked and as
 * {@link souther.compiler.core.Core} where the rules are discharged, and both ask what a written
 * value comes to.
 *
 * <p><b>One account of the arithmetic, because two would disagree.</b> Overflow aborts rather than
 * wrapping, a quotient is exact, a {@code Decimal} compares by amount and not by how it was
 * written, and a comparison answers what its operator placed. Each of those is a rule about the
 * language rather than about a representation, so a second walk that arrived at its own would be a
 * program folding one way where it is checked and another where it is discharged.
 *
 * <p>Nothing here reaches a name. A constant arrives already worked out, and what a name stands for
 * is the environment's answer (ADR-0106, ADR-0111) — asked by the walk, before it gets here.
 */
final class ConstantAlgebra {

    private ConstantAlgebra() {}

    /**
     * The negation of a folded number, over every number a fold reaches.
     *
     * <p>The exact one among them for the reason the binary arms admit it: negation answers the type
     * it is given, so a value this reads and cannot negate would be a constant that stops being one
     * for the way it was bracketed — {@code -1 / 2} folding where {@code -(1 / 2)} does not, of the
     * same number.
     */
    static Optional<Object> negate(Object o) {
        if (o instanceof Long x) {
            return Optional.of(-x);
        }
        if (o instanceof BigDecimal d) {
            return Optional.of(d.negate());
        }
        if (o instanceof ExactRatio r) {
            return Optional.of(r.negated());
        }
        return Optional.empty();
    }

    /**
     * What {@code op} answers from its left operand alone, or empty where it needs the other one.
     *
     * <p>{@code &&} and {@code ||} settle on their left operand, and what settles them is the answer
     * whatever the right operand is. Read eagerly, a right operand a walk cannot fold would take a
     * settled condition down with it — so a construction the language calls constant would be
     * checked where it was written one way and not the other.
     *
     * <p>Asked here rather than decided by each walk, because which operators do this is a fact
     * about the operators. What the walk does with the answer is its own: it is what says whether
     * the other operand is read at all.
     */
    static Optional<Object> settledByTheLeft(BinOp op, Object left) {
        if (!(left instanceof Boolean settled)) {
            return Optional.empty();
        }
        return (op == BinOp.AND && !settled) || (op == BinOp.OR && settled)
                ? Optional.of(settled) : Optional.empty();
    }

    /** What {@code op} makes of two constants, or empty where these two do not answer it. */
    static Optional<Object> binary(BinOp op, Object a, Object b) {
        // A comparison folds through what its operator placed, and this is where the operator's
        // words are left behind: what such an expression comes to is the relation it states of its
        // two sides, which is the one answer a reading that never had an operator asks for as well.
        if (ComparisonPlacement.of(op) instanceof ComparisonClaim placed) {
            return Optional.ofNullable(stands(placed.statedRelation(), a, b));
        }
        return switch (op) {
            case AND -> a instanceof Boolean x && b instanceof Boolean y
                    ? Optional.of(x && y) : Optional.empty();
            case OR -> a instanceof Boolean x && b instanceof Boolean y
                    ? Optional.of(x || y) : Optional.empty();
            case ADD, SUB, MUL -> arith(op, a, b);
            // `++` appends two strings or two lists (spec §an-operator-takes-the-types-it-is-defined-for);
            // the string case folds, and a list is not a constant here to begin with. Canonicalized,
            // the same seam String.append/Strings.append has: a folded `"a" ++ pad` and the same
            // expression run at the runtime it would otherwise be compiled to cannot answer
            // differently just because one of them happened at compile time.
            case CONCAT -> a instanceof String x && b instanceof String y
                    ? Optional.of(Normalization.nfc(x + y)) : Optional.empty();
            case DIV -> quotient(a, b);
            // Answered above as what it placed. Written out rather than left to a default, because
            // what would arrive here is the partition above having admitted a comparison into the
            // arms that compute a value, and an arm inventing an answer for that is how a fold
            // comes to disagree with every other reader of the same comparison.
            case EQ, NE, LT, LE, GT, GE -> throw new IllegalStateException(
                    "a comparison is folded from what it placed, not from " + op);
        };
    }

    /**
     * Whether {@code rel} holds between two folded constants, or {@code null} where these two
     * cannot answer it.
     *
     * <p>The whole of what a comparison of written values comes to, whichever words the caller has
     * it in. A reading that composed a comparison out of what the rules proved has no operator and
     * no node — it has what the comparison places and its two sides — and an expression written with
     * an operator arrives with the relation that operator placed
     * ({@link ComparisonClaim#statedRelation}). One fold under the crossing, rather than one on
     * either side of it agreeing about every pair of constants there is until somebody edits one.
     *
     * <p>An ordering answers where the two are of one ordered kind, and an equality answers of any
     * two constants at all: {@code true == true} is decided where {@code true < true} is not
     * something to decide.
     *
     * <p><b>Which way the two stand is worked out here and goes nowhere.</b> A sign handed back to a
     * caller is what a second table of six is written over — {@code c < 0} and the three beside it
     * are the same table as {@link Rel#holds} in another hand — so the order of two constants is
     * taken and answered in the one place, and there is nothing to call for the sign alone.
     */
    static Boolean stands(Rel rel, Object a, Object b) {
        // A comparison one side of which holds a ratio is decided on the exact values, which is the
        // same rule the operator states (ADR-0116). Asked before the two same-kind arms below and
        // only where a ratio is in hand, so that an `Int` beside a `Decimal` is still two kinds with
        // nothing between them.
        if (eitherIsExact(a, b)) {
            ExactRatio x = exactly(a);
            ExactRatio y = exactly(b);
            return (x == null || y == null) ? null : rel.holds(x.compareTo(y));
        }
        if (a instanceof Long x && b instanceof Long y) {
            return rel.holds(Long.compare(x, y));
        }
        if (a instanceof BigDecimal x && b instanceof BigDecimal y) {
            return rel.holds(x.compareTo(y));
        }
        if (a instanceof String x && b instanceof String y) {
            return rel.holds(ScalarValues.compare(x, y));
        }
        return switch (rel) {
            case EQ -> equal(a, b);
            case NE -> !equal(a, b);
            case GE, GT, LE, LT -> null;
        };
    }

    /**
     * Whether two folded values are the one value. A {@code Decimal} answers by amount and not by
     * how it was written, as it does everywhere else: {@code 1.0m} and {@code 1.00m} are one number,
     * and a comparison folding the other way would decide at compile time what the run time denies.
     *
     * <p>Asked outside a fold too — holding two builds' declarations against each other asks it of
     * every literal they state ({@code DeclarationAgreement}). Asked of this rather than answered
     * again there: a second answer is the rule restated, and a restatement is what goes wrong the
     * day the rule moves.
     */
    static boolean equal(Object a, Object b) {
        if (a instanceof BigDecimal x && b instanceof BigDecimal y) {
            return x.compareTo(y) == 0;
        }
        return a.equals(b);
    }

    /**
     * What {@code kernel} computes of arguments already folded, or empty where it computes nothing
     * here.
     *
     * <p>Keyed by the kernel the library declares an operation to be and not by the name it is
     * published under: the three below fold because of what they compute, and a fold selected by an
     * alias would be right for exactly as long as the two agreed.
     */
    static Optional<Object> computed(Kernel kernel, List<Object> args) {
        switch (kernel) {
            case STRING_LENGTH -> {
                if (args.size() == 1 && args.get(0) instanceof String s) {
                    return Optional.of(ScalarValues.count(s));
                }
            }
            // matches(pattern, s): the pattern is written first and the subject last (spec §pipe).
            // The pattern of a declaration is already required to be a written constant, so a call
            // over a written subject is one the compiler answers rather than the run time.
            case STRING_MATCHES -> {
                if (args.size() == 2 && args.get(0) instanceof String pattern
                        && args.get(1) instanceof String s) {
                    return matches(pattern, s);
                }
            }
            case STRING_CONTAINS -> {
                // contains(sub, s): the string being searched is the last argument (spec §pipe)
                if (args.size() == 2 && args.get(0) instanceof String sub
                        && args.get(1) instanceof String s) {
                    return Optional.of(s.contains(sub));
                }
            }
            default -> { }
        }
        return Optional.empty();
    }

    /**
     * The quotient of two written numbers, or empty where this is not the one to answer it.
     *
     * <p>The quotient is exact, so what it folds to is a ratio and not a number of either operand's
     * type (ADR-0116). There is no pair of whole numbers whose exact quotient is out of range and
     * none whose fraction is dropped, so the two refusals the truncating quotient needed are gone
     * with it; what is left is the divisor of nought, which the run time aborts on and which no value
     * handed back would be about.
     *
     * <p>Two decimals go through the same reading, their quotient being exact as well. What the fold
     * answers is the ratio, so a written {@code 1.0m / 3.0m} comes to a third here and not to the
     * number of places somebody would have had to choose for it.
     */
    private static Optional<Object> quotient(Object a, Object b) {
        ExactRatio x = exactly(a);
        ExactRatio y = exactly(b);
        if (x == null || y == null || y.isZero()) {
            return Optional.empty();
        }
        return Optional.of(x.dividedBy(y));
    }

    /**
     * The exact value of a folded number, or null where the constant is not one.
     *
     * <p>What it is for is the arithmetic a Rational operand makes exact: the operand beside it is
     * read at its exact mathematical value because that is what the operator means, and the fold has
     * to read it the same way or a constant expression and the same expression at run time would
     * answer differently. It is no conversion between the two numeric types — nothing here brings a
     * {@code Decimal} and an {@code Int} together, and the callers ask only where one side already
     * holds a ratio.
     */
    private static ExactRatio exactly(Object constant) {
        return switch (constant) {
            case ExactRatio r -> r;
            case Long whole -> ExactRatio.of(whole);
            case BigDecimal written -> ExactRatio.of(written);
            default -> null;
        };
    }

    /** Whether either side of an operator already holds an exact ratio, which is what makes that
     *  operation exact arithmetic (ADR-0116). */
    private static boolean eitherIsExact(Object a, Object b) {
        return a instanceof ExactRatio || b instanceof ExactRatio;
    }

    private static Optional<Object> arith(BinOp op, Object a, Object b) {
        if (eitherIsExact(a, b)) {
            ExactRatio x = exactly(a);
            ExactRatio y = exactly(b);
            if (x == null || y == null) {
                return Optional.empty();
            }
            return Optional.of(switch (op) {
                case ADD -> x.plus(y);
                case SUB -> x.minus(y);
                case MUL -> x.times(y);
                default -> throw new IllegalStateException();
            });
        }
        if (a instanceof Long x && b instanceof Long y) {
            // The same kernels the operators emit: an Int that overflows aborts rather than wrapping,
            // so a fold that wrapped would answer what the run time refuses to compute.
            try {
                return Optional.of(switch (op) {
                    case ADD -> Math.addExact(x, y);
                    case SUB -> Math.subtractExact(x, y);
                    case MUL -> Math.multiplyExact(x, y);
                    default -> throw new IllegalStateException();
                });
            } catch (ArithmeticException _) {
                return Optional.empty();
            }
        }
        if (a instanceof BigDecimal x && b instanceof BigDecimal y) {
            return Optional.of(switch (op) {
                case ADD -> x.add(y);
                case SUB -> x.subtract(y);
                case MUL -> x.multiply(y);
                default -> throw new IllegalStateException();
            });
        }
        return Optional.empty();
    }

    /**
     * Whether {@code s} matches {@code pattern}, or empty where this fold does not settle it.
     *
     * <p>Answered by the language the pattern means, the one the analysis reads and every output
     * lowers, so what the compiler folds a call to is what the run time answers for it. A walk over
     * a machine reads each symbol once, so what could be expensive is building the machine, and
     * that is what the allowance bounds.
     *
     * <p>Reached from the written tree, where no call has been settled yet, so the text is read here
     * by the language's reader. A checked tree carries the meaning on the call and folds through
     * {@link #matching} without reading any text.
     *
     * <p>Empty for text that is no pattern of the language and for a pattern deeper than the
     * compiler reads: both are refused where the call is checked, and a fold reached before that
     * check has nothing to answer with. None of them is an answer about the program.
     */
    private static Optional<Object> matches(String pattern, String s) {
        return PatternParser.read(pattern) instanceof PatternRead.Read read
                ? matching(read.meaning(), s) : Optional.empty();
    }

    /**
     * Whether {@code s} is one of the strings {@code meaning} denotes, or empty where the machine for
     * it is more than a fold may build — which leaves the match to the run time.
     */
    static Optional<Object> matching(PatternMeaning meaning, String s) {
        return RECOGNIZERS.computeIfAbsent(meaning, ConstantAlgebra::recognizerOf)
                .map(recognizer -> recognizer.accepts(s));
    }

    private static Optional<Recognizer> recognizerOf(PatternMeaning meaning) {
        return Optional.ofNullable(Recognizer.of(meaning, PatternPlan.Budget.OF_A_FOLD.meter()));
    }

    /** What each pattern means, as the machine a fold walks. A declaration's pattern is asked about
     * once per construction from it and once per reading of a branch, and building the machine is
     * the only expensive thing here. Keyed by the meaning, so two spellings of one pattern are one
     * machine. */
    private static final Map<PatternMeaning, Optional<Recognizer>> RECOGNIZERS =
            new ConcurrentHashMap<>();
}
