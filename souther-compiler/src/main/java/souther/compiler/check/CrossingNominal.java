package souther.compiler.check;

import souther.compiler.types.TypeSymbol;

import java.util.Objects;

/**
 * A named type admitted as one a model declares, where an external representation crosses.
 *
 * <p>The rule is the specification's: a named type that crosses MUST be one a model declares
 * (spec {@code [#a-boundary-carries-the-models-own-vocabulary]}). The language declares vocabulary of
 * its own — the case a division by zero answers with, the rounding mode a {@code Decimal} operation
 * takes, the reserved {@code Raw} — and those say what one of its operations can answer or take,
 * not what a model publishes.
 *
 * <p>What crosses is not only a behavior's boundary. A data field crosses, at any depth inside a
 * collection, and so does the base a newtype is written from, since a newtype hands its whole input
 * to that base's decoder (spec {@code [#collections]}, {@code [#newtype]}). Those positions are
 * walked by {@code CodecShape} and a behavior's by {@link SignatureBoundary}; the walks stay apart,
 * because each owns what it admits at every other position and how it words a refusal. This is the
 * one proposition they share, and holding it is what makes it shared rather than restated.
 *
 * <p>Not "a codec exists for this name". That a codec exists is a consequence of the rule under the
 * language as it stands — every declaration a module of this compilation writes gets one, and the
 * language's own vocabulary is kept out of derivation — and reading the consequence for the rule is
 * what {@code DataChecker} did when it asked whether a decoder node sat on a declaration. A unit data
 * carries no such node and is a model's own word, so it crosses; {@code RoundingMode} classifies as
 * a boundary map key and is the language's, so it does not. Supplying a codec would not change
 * either answer.
 *
 * <p>Closed, and made by {@link #admitted} alone. A name is a thing that is admitted or refused, and
 * anything holding a {@link TypeSymbol} could otherwise assemble a witness every reader below takes
 * for one the compiler stands behind — which is the reading ADR-0100 settled for a signature and the
 * one this settles for everything else that crosses.
 */
public final class CrossingNominal {

    private final TypeSymbol name;

    private CrossingNominal(TypeSymbol name) {
        this.name = name;
    }

    /**
     * The name where a model declares it, and null everywhere else.
     *
     * <p>The language's own namespace answers null throughout, and not only for the names that stand
     * for something. A primitive's name is not a declaration to admit: it is how a scalar sits in a
     * union ({@code Int | DivisionByZero}), and a position that can meet one admits it as the scalar
     * it is — which is also where {@code Raw} is refused, having no scalar to be. {@code Some} and
     * {@code None} live in that namespace and stand for no primitive at all, and any spelling can be
     * minted into it, so admitting the namespace would put this type's domain wider than the rule it
     * is named for.
     *
     * <p>A name outside it is asked of the declaration world, which tells a module's declarations
     * from the language's: the prelude's runtime-backed data resolves and types like any other and
     * belongs to no module here.
     */
    public static CrossingNominal admitted(TypeSymbol name, Symbols symbols) {
        if (name.isPrimitive()) {
            return null;
        }
        return symbols.declarations().declaredByCompilation(name.key())
                ? new CrossingNominal(name)
                : null;
    }

    /** Which declaration this is. */
    public TypeSymbol name() {
        return name;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof CrossingNominal n && name.equals(n.name);
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(name);
    }

    @Override
    public String toString() {
        return "CrossingNominal[name=" + name + "]";
    }
}
