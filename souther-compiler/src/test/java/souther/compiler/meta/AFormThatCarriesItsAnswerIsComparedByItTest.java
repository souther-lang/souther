package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.types.BindingId;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenTypeMeaning;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A form that carries both a spelling and what the front end settled it to be is compared by the
 * answer, and every such form is one {@link DeclarationAgreement} was told about.
 *
 * <p>There is one rule about names and this is it. Where the front end put the answer beside the
 * spelling — a use with its {@link ValueName}, a type with its {@link TypeSymbol}, a binding with
 * its {@link BindingId} — the answer is compared and the spelling is passed over, which is what
 * makes an alias and a name written out in full one name. Everywhere else the spelling is the
 * meaning: which field a value is read under is that word, and a decoder reads it by that word.
 *
 * <p>So the failure this catches is a form that grows an answer and goes on being compared by how it
 * was written. That reports a build as moved over a spelling, which is noisy but visible. The
 * opposite — passing over a spelling nothing else answers for — is what the default guards against,
 * and it is the one that is silent: {@code r.min} and {@code r.max} would agree, and a row would go
 * to an answer that refuses what this model admits.
 *
 * <p>Read off the forms rather than from a list kept here, so a form the language gains is measured
 * rather than remembered.
 */
class AFormThatCarriesItsAnswerIsComparedByItTest {

    /** What the comparison is handed. */
    private static final List<Class<?>> ROOTS = List.of(
            Hir.Data.class, Hir.SumData.class, Hir.UnitData.class,
            Hir.SpecBehavior.class, Hir.PipeBehavior.class, Hir.FnDef.class);

    @Test
    void everyFormCarryingBothIsComparedByTheAnswer() {
        List<String> carrying = new ArrayList<>(new TreeSet<>(reachable().stream()
                .filter(DeclarationAgreement::carriesItsAnswerBesideItsSpelling)
                .map(Class::getName)
                .toList()));

        assertEquals(List.of(
                        // A binding is the binding it is, whatever it is called.
                        "souther.compiler.ast.Hir$Binder",
                        // A type named is the declaration it names.
                        "souther.compiler.ast.Hir$Name$Denoting",
                        // A type reference is the type it refers to.
                        "souther.compiler.ast.Hir$TypeRef",
                        // A use is what it denotes.
                        "souther.compiler.ast.Hir$Var$Denoting",
                        // A local is the binding it is; a type used as a value is that type.
                        "souther.compiler.types.ValueName$Local",
                        "souther.compiler.types.ValueName$OfType"),
                carrying,
                "each of these carries a spelling and the answer the front end settled beside it, so"
                        + " each has an arm in `sameShape` comparing it by the answer. A form here"
                        + " with no arm is compared by how it was written");
    }

    /**
     * The control for the walk: it goes through a form of the grammar that is not a record.
     *
     * <p>What a written type comes to is held nowhere else, so reaching it says the walk went
     * through the written type rather than stopping at it. Most of what a form holds is held by some
     * other form too, and a walk that stopped would go on finding those by the other route and
     * saying nothing — which is how this test went on passing while the set it was reading over got
     * smaller.
     */
    @Test
    void andTheWalkGoesThroughAFormOfTheGrammarThatIsNotARecord() {
        assertTrue(reachable().contains(WrittenTypeMeaning.Settled.class),
                "what a written type comes to is reached through the written type and nowhere"
                        + " else, so a walk that stops at one never sees it");
    }

    /** The control: the walk can tell a form that carries only a spelling from one that carries both. */
    @Test
    void andAFormCarryingOnlyASpellingIsNotAmongThem() {
        assertFalse(DeclarationAgreement.carriesItsAnswerBesideItsSpelling(Hir.Field.class),
                "a field carries what it is called and nothing that says what that means, so the"
                        + " word is the meaning");
        assertFalse(DeclarationAgreement.carriesItsAnswerBesideItsSpelling(Hir.FieldAccess.class),
                "and so is the field a value is read under");
    }

    /**
     * A declaration's own name is its key and not a spelling to pass over, so the three declaration
     * forms are not among the ones compared by an answer: the comparison pairs them by name before
     * comparing anything of them.
     */
    @Test
    void andADeclarationsOwnNameIsNotASpellingPassedOver() {
        for (Class<?> declaration
                : List.of(Hir.Data.class, Hir.SumData.class, Hir.UnitData.class)) {
            assertFalse(DeclarationAgreement.carriesItsAnswerBesideItsSpelling(declaration),
                    declaration.getSimpleName() + " is reached by its name, so the name is what it"
                            + " is held by and not a spelling something else answers for");
        }
    }

    /** Every form reachable from a declaration. */
    private static Set<Class<?>> reachable() {
        Set<Class<?>> seen = new LinkedHashSet<>();
        Deque<Class<?>> todo = new ArrayDeque<>(ROOTS);
        while (!todo.isEmpty()) {
            Class<?> type = todo.removeFirst();
            if (!seen.add(type) || type.isPrimitive()) {
                continue;
            }
            if (type.isSealed()) {
                todo.addAll(List.of(type.getPermittedSubclasses()));
                continue;
            }
            if (!StructuralParts.areHandedOver(type)) {
                continue;
            }
            for (StructuralParts.Part part : StructuralParts.of(type)) {
                todo.addAll(StructuralParts.held(part.held()));
            }
        }
        return seen;
    }
}
