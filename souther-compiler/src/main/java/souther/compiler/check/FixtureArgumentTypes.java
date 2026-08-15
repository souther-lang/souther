package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;

/**
 * What each argument a fixture wrote is already known to be.
 *
 * <p>Evidence, not inference. An argument's type is one something else settled — a declaration
 * ({@link FixtureEvidence}: a construction names its type, a field is declared one, a name stands
 * for a body that is), or the language's reading of a written literal, which {@link Elaborator}
 * makes an {@code Int} of {@code 1} wherever it stands. Nothing here works a type out.
 *
 * <p>An application is not read, and that is the one exclusion worth stating: a construction written
 * in call form <em>is</em> read, because a newtype's name is its declaration and no answer is being
 * predicted. What a helper answers with is its answer's to say, and deriving it from the declaration
 * here would be a second reading of a call the language already elaborates one way. What widens the
 * range read here is a fixture expression that can be asked what elaboration made of it, and nothing
 * short of that.
 */
public final class FixtureArgumentTypes {

    private FixtureArgumentTypes() {
    }

    /**
     * The type each argument of {@code call} states, in order, null where an argument states none.
     *
     * <p>Null says one thing and is not asked to say more: there is no type evidence here to settle
     * a variable with. Whether that is because the writing has no type of its own, because what has
     * one is not read here, or because it is not a writing at all are different questions, and the
     * caller asks none of them — a variable nothing settled is refused by its own name either way.
     * Telling them apart is worth a type of its own only when a reader would do something different
     * with each.
     */
    public static List<Type> of(Hir.Apply call, FixtureEvidence evidence) {
        List<Type> stated = new ArrayList<>();
        for (Hir.Expr arg : call.args()) {
            stated.add(stated(arg, evidence));
        }
        return stated;
    }

    /** The type one written value states. */
    public static Type stated(Hir.Expr e, FixtureEvidence evidence) {
        Type declared = evidence.declaredTypeOf(e);
        if (declared != null) {
            return declared;
        }
        return switch (e) {
            case Hir.IntLit _ -> Type.INT;
            case Hir.DecimalLit _ -> Type.DECIMAL;
            case Hir.StringLit _ -> Type.STRING;
            case Hir.BoolLit _ -> Type.BOOL;
            // A written list states what its elements state. Where they disagree, or where there
            // are none, nothing was stated: `[]` says what it holds nowhere, and a call that needed
            // it to is refused for the variable that stayed open rather than for the empty list.
            case Hir.ListLit l -> {
                Type element = agreedOn(l.elements(), evidence);
                yield element == null ? null : Type.list(element);
            }
            case Hir.RowCollection row -> {
                Type element = agreedOn(row.elements(), evidence);
                yield element == null ? null : Type.list(element);
            }
            case null, default -> null;
        };
    }

    /** The one type every element states, or null where they state none or state several. */
    private static Type agreedOn(List<Hir.Expr> elements, FixtureEvidence evidence) {
        Type agreed = null;
        for (Hir.Expr e : elements) {
            Type stated = stated(e, evidence);
            if (stated == null || (agreed != null && !agreed.equals(stated))) {
                return null;
            }
            agreed = stated;
        }
        return agreed;
    }
}
