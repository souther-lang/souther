package souther.compiler.check;

import souther.compiler.semantics.NumericResult;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

/**
 * The type of the number one of the language's operations answers.
 *
 * <p><b>The one entry, so that a caller never assembles this itself.</b> Three things have a say —
 * the library's signature, whether the number stands in the result or in one case of it
 * ({@link NumericResult.Answered}), and nothing else — and a caller that read the signature alone
 * would be right for every operation until the first that answers its number inside a union, and
 * wrong there without saying so.
 *
 * <p>What this is for is the carrier of a term standing for such an answer. What a number is
 * measured by follows from what the number <em>is</em>, and what it is is declared by the operation:
 * {@code String.length} answers an {@code Int} and steps by one, {@code Decimal.abs} answers a
 * {@code Decimal} and does not. Taken from the position the operation was applied at instead, the
 * step of the answer was the step of the argument — the same carrier for {@code Date.year(d)} as
 * for {@code d} — which is a boundary sharpened onto a value the term never takes (#1027).
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
        NumericResult computed = OperationFacts.computesANumber(operation);
        if (computed != null
                && computed.at() instanceof NumericResult.Answered.InTheCaseCarrying carrying) {
            return carrying.carried();
        }
        return entry.signature().result();
    }

    /** The same, for a reader already holding the symbols its module was compiled against. */
    public static Type typeOf(ValueName operation, Symbols symbols) {
        return typeOf(operation, symbols.library());
    }

    private NumericAnswers() {}
}
