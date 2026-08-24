package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.semantics.Arithmetic;

import java.util.List;

/**
 * The term a call computes, out of the arithmetic its operation is and the arguments it was given.
 *
 * <p>Which arithmetic an operation is, is a fact about the operation and is declared with the rest
 * of them. Building a term from a particular call's arguments is a reading, and this is where the
 * two meet — the same division {@link CallArguments} makes for an argument a fact names.
 *
 * <p>The order the arguments are read in comes from the arithmetic, which states what each of them
 * has to be. Read here instead, which argument is the divisor would be settled twice.
 */
final class NumericMeanings {

    /** What a call handing over {@code args} to {@code arithmetic} computes. */
    static NumericMeaning of(Arithmetic arithmetic, List<Core> args) {
        return switch (arithmetic) {
            case Arithmetic.TheOperator operator ->
                    new NumericMeaning.Operator(operator.op(), args.get(0), args.get(1));
            case Arithmetic.ATruncatingQuotient _ ->
                    new NumericMeaning.TruncatingQuotient(args.get(0), args.get(1));
            case Arithmetic.ATruncatingRemainder _ ->
                    new NumericMeaning.TruncatingRemainder(args.get(0), args.get(1));
            case Arithmetic.AQuotientRoundedToAScale _ -> new NumericMeaning.RoundedQuotient(
                    args.get(0), args.get(1), args.get(2), args.get(3));
        };
    }

    private NumericMeanings() {}
}
