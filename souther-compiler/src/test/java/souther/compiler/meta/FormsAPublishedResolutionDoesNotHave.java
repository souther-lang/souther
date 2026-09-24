package souther.compiler.meta;

import souther.compiler.ast.Hir;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Map;
import java.util.LinkedHashMap;

/**
 * The forms of the grammar a published declaration is never read back as.
 *
 * <p>A declaration travels as source. What a module publishes is put back together as one text and
 * handed to the parser, and what comes back is what scoping and resolution make of it
 * ({@link ModuleReadback}, {@link PublishedUniverse}) — so the forms a crossing can meet are the
 * ones that reading produces. The passes below resolution build forms of their own out of what it
 * answered, and those are in the tree this compile goes on to check and emit from. They are not in
 * the one a crossing is handed.
 *
 * <p><b>Said here rather than worked out.</b> A form and the pass that builds it sit in one sealed
 * hierarchy with nothing to tell them apart: an expansion is written beside an application and is as
 * public as one, and no type, marker or constructor says which phase makes which. A sweep that read
 * the passes instead would be deciding which forms there are from which classes happen to call
 * which constructor today, which is an account taken from somewhere other than a decision — and is
 * the shape of the defect this whole reading keeps arriving at.
 *
 * <p><b>What this is not.</b> It says nothing about how a crossing compares one of these, because a
 * form a crossing never meets has nothing to be compared by. Giving one a comparison rule would be
 * writing a rule nobody can read the truth of.
 *
 * <p>What keeps it honest is beside it and not in it:
 * {@code WhoMayBuildAFormNoPublishedResolutionHasTest} holds the classes that build one of these to
 * a written list, so a pass that begins building one — resolution among them — is a row nobody
 * wrote. That control cannot see the other way this could go false, which is one of the classes
 * already on the list coming to run while a module is read back. That residue is this account's to
 * carry.
 */
final class FormsAPublishedResolutionDoesNotHave {

    private FormsAPublishedResolutionDoesNotHave() {}

    /** Each form, and why a published declaration is never read back as one. */
    private static final Map<Class<?>, String> NOT_READ_BACK_AS = notReadBackAs();

    private static Map<Class<?>, String> notReadBackAs() {
        Map<Class<?>, String> said = new LinkedHashMap<>();
        said.put(Hir.Expansion.class,
                "a helper expanded into the body that calls it, which is a copy a pass below"
                        + " resolution makes. What a module publishes of a helper is the helper,"
                        + " and whoever reads it expands it for themselves; the expansion is in"
                        + " the reader's tree and never in what crossed.");
        said.put(Type.MetaVar.class,
                "a variable one application of a signature left open, waiting for that application"
                        + " to decide it. It lives no longer than the elaboration that made it —"
                        + " decided there, or read as nothing at its boundary — so no answer this"
                        + " compiler stores holds one, and a declaration read back out of what was"
                        + " stored cannot.");
        return said;
    }

    /** Whether a published declaration can be read back as one of these. */
    static boolean canBeReadBackAs(Class<?> form) {
        return !NOT_READ_BACK_AS.containsKey(form);
    }

    /** The forms, for a reader holding them to something. */
    static List<Class<?>> theOnesItCannot() {
        return List.copyOf(NOT_READ_BACK_AS.keySet());
    }

}
