package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
import souther.compiler.types.BindingId;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
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

    /**
     * A declaration's own name is its key and not a spelling to pass over, so the three declaration
     * forms are not among the ones compared by an answer. They are paired by name before anything
     * of them is compared.
     */
    private static final Set<String> COMPARED_BY_NAME = Set.of(
            Hir.Data.class.getName(), Hir.SumData.class.getName(), Hir.UnitData.class.getName());

    @Test
    void everyFormCarryingBothIsComparedByTheAnswer() {
        List<String> carrying = new ArrayList<>(new TreeSet<>(reachable().stream()
                .filter(AFormThatCarriesItsAnswerIsComparedByItTest::carriesASpellingAndItsAnswer)
                .map(Class::getName)
                .filter(name -> !COMPARED_BY_NAME.contains(name))
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
        assertFalse(carriesASpellingAndItsAnswer(Hir.Field.class),
                "a field carries what it is called and nothing that says what that means, so the"
                        + " word is the meaning");
        assertFalse(carriesASpellingAndItsAnswer(Hir.FieldAccess.class),
                "and so is the field a value is read under");
    }

    /**
     * And what the comparison names as read by the answer is those and no others.
     *
     * <p>The two sides of one thing. Above says a form with the shape has an arm; this says the
     * arms are for forms with the shape, so the naming beside the comparison cannot grow a form the
     * comparison reads by how it was written — which would refuse a set of them for a reason that
     * is not there.
     */
    @Test
    void andTheArmsAreNamedForThoseAndNoOthers() {
        for (Class<?> form : reachable()) {
            assertEquals(carriesASpellingAndItsAnswer(form)
                            && !COMPARED_BY_NAME.contains(form.getName()),
                    DeclarationAgreement.readByTheAnswerBesideItsSpelling(form),
                    form.getName() + " is read by the answer beside its spelling, or it is not, and"
                            + " what the comparison does with it and what it is made of have to"
                            + " say the same thing");
        }
    }

    /** Whether {@code form} holds a spelling and, beside it, what that spelling was settled to be. */
    private static boolean carriesASpellingAndItsAnswer(Class<?> form) {
        if (!StructuralParts.areHandedOver(form)) {
            return false;
        }
        boolean spelling = false;
        boolean answer = false;
        for (StructuralParts.Part part : StructuralParts.of(form)) {
            Class<?> held = part.held() instanceof Class<?> plain ? plain : null;
            spelling |= held == WrittenName.class || held == String.class;
            answer |= held == TypeSymbol.class || held == ValueName.class
                    || held == BindingId.class || held == Type.class
                    // A use is settled to a reference, which carries the declaration it reaches.
                    // Read for the same reason `ValueName` is: what the front end put beside the
                    // spelling is the answer, whether the answer is the declaration or the
                    // reference that reached it.
                    || held == ReachName.class;
        }
        return spelling && answer;
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
                todo.addAll(TypesAPartIsDeclaredToHold.named(part.held()));
            }
        }
        return seen;
    }
}
