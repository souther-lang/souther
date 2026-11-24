package souther.compiler.check;

import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

/**
 * The number a statement about an operation's arithmetic is about.
 *
 * <p>Wider than {@link NumericAnswers}, which is the number a term can stand for and so a number
 * on a carrier. What an operation computes, as a form of its arguments or as an operator's
 * arithmetic, is a statement about exact values, and a {@code Rational} has one though no carrier
 * counts it ({@link BinaryElaborator#exactlyReadable}). The two are kept apart so that widening
 * the first never gives a term a number no position holds, and narrowing it never takes the second
 * from a statement that is true of the arithmetic.
 *
 * <p>The one place that says which number such a statement is about: the binder holds a declared
 * arithmetic to it, and the count of representations that read an operation's number
 * ({@link NumericReadings}) asks it, so a statement the binder accepts is a statement that count
 * sees.
 */
final class ArithmeticAnswers {

    /**
     * The number {@code t} is, or the one number a union of it holds as a case — or null where it
     * holds none, or holds two, which of them a statement was written for being nothing a row
     * has a column for.
     */
    static Type in(Type t) {
        if (BinaryElaborator.exactlyReadable(t)) {
            return t;
        }
        if (!(t instanceof Type.Union union)) {
            return null;
        }
        Type found = null;
        for (TypeSymbol member : union.members()) {
            Type.Prim prim = member.primitiveKind();
            if (prim != null && BinaryElaborator.exactlyReadable(prim)) {
                if (found != null) {
                    return null;
                }
                found = prim;
            }
        }
        return found;
    }

    /**
     * Whether {@code operation} answers a number for some value it could be given, which is the
     * question a reader of declarations can ask ({@link NumericAnswers#typeOf} is the one a reader
     * of a call can).
     *
     * <p>A sum over a list of text answers no number and is the same operation as a sum over a list
     * of whole numbers, so an operation refused here would be refused for every call including the
     * ones that do answer one. Accumulating is not on its own enough: a join of strings walks a
     * container from an identity through a step exactly as a sum does, and what it answers is
     * declared.
     */
    static boolean mayAnswer(BoundOperationFacts facts, ValueName.Stdlib.Operation named,
                             Stdlib.Signature signature) {
        if (in(signature.result()) != null) {
            return true;
        }
        return facts.accumulation(named) != null
                && NumericAnswers.answerIsLeftToTheCall(signature.result());
    }

    private ArithmeticAnswers() {}
}
