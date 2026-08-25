package souther.compiler.check;

import souther.compiler.semantics.NumericResult;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

/**
 * The type of the number one of the language's operations answers.
 *
 * <p><b>The one entry, so that a caller never assembles this itself.</b> Two things have a say — the
 * library's signature and the shape of what it answers — and a caller that took the result type as
 * it stands would be right for every operation until the first that answers its number inside a
 * union, and wrong there without saying so.
 *
 * <p>Read by three kinds of reader and owned by none of them: what puts an operation in range of a
 * question ({@link Question}), what holds a declared fact to the signature it is about
 * ({@link DischargeRules}), and what lists the representations reading a number
 * ({@link NumericReadings}). Answered inside any one of them, the other two borrow a consumer's
 * answer, and a reader that would rather not borrow writes a second answer — which agrees with the
 * first everywhere except a union, where nothing brings the two together to disagree.
 *
 * <p>What this is for is the carrier of a term standing for such an answer. What a number is
 * measured by follows from what the number <em>is</em>, and what it is is declared by the operation:
 * {@code String.length} and {@code Time.hour} both answer an {@code Int} and step by one, at
 * positions that step by a character and by a second. Taken from the position the operation was
 * applied at instead, the step of the answer was the step of the argument — a line at the twelfth
 * hour drawn at the twelfth second — which is a boundary sharpened onto a value the term never
 * takes (#1027).
 *
 * <p>Here rather than beside the declarations because reading a signature is the frontend's. A fact
 * is a proposition about an operation and is declared where those are; what the library was written
 * to declare is read where the library is read.
 */
public final class NumericAnswers {

    /**
     * The type of the number {@code operation} answers, or null where it answers none this can
     * name.
     *
     * <p>Null and not a refusal. Whether an operation answers a number at all is a question askable
     * of any name, and the callers that ask it are asking whether there is a term here — an answer
     * they have somewhere to put.
     */
    public static Type typeOf(ValueName operation, Stdlib library) {
        if (!(operation instanceof ValueName.Stdlib named) || named.isNamespace()) {
            return null;
        }
        Stdlib.Entry entry = library.entry(named.qualified());
        if (entry == null || entry.signature() == null) {
            return null;
        }
        return in(entry.signature().result());
    }

    /**
     * The number a result of {@code t} answers — {@code t} itself where it is one, and the number a
     * union carries where exactly one of its cases is a number.
     *
     * <p>Exactly one, and not the first found. A union carrying two numbers would answer its number
     * at two cases, and which of them a statement about the operation was written for is a question
     * nothing here has a column for — so it answers none, and goes on answering none until something
     * says which.
     *
     * <p>Read off the result and not off what is declared of the operation. What arithmetic an
     * operation computes says where <em>that</em> arithmetic is answered
     * ({@link NumericResult.Answered.InTheCaseCarrying}), which is a different sentence: an
     * operation answering {@code Int | Decimal | SomeError} carries two numbers whatever its
     * arithmetic names, and taking the arithmetic's case for the number the operation answers would
     * make a proposition about one representation into the answer for all of them. The two are held
     * to each other where the arithmetic is declared, so a case naming a number this does not find
     * is refused rather than believed.
     */
    static Type in(Type t) {
        if (isANumber(t)) {
            return t;
        }
        if (!(t instanceof Type.Union union)) {
            return null;
        }
        Type found = null;
        for (souther.compiler.types.TypeSymbol member : union.members()) {
            Type.Prim prim = member.primitiveKind();
            if (prim != null && isANumber(prim)) {
                if (found != null) {
                    return null;
                }
                found = prim;
            }
        }
        return found;
    }

    /** Whether {@code t} is one of the kinds of number the domain relates arithmetically. Read where
     * the numeric rules are bound as well: what such a rule may be written about is the same question
     * as what puts an operation in range of one. */
    static boolean isANumber(Type t) {
        return t == Type.Prim.INT || t == Type.Prim.DECIMAL;
    }

    /** The same, for a reader already holding the symbols its module was compiled against. */
    public static Type typeOf(ValueName operation, Symbols symbols) {
        return typeOf(operation, symbols.library());
    }

    private NumericAnswers() {}
}
