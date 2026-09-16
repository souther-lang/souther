package souther.compiler.meta;

import souther.compiler.ast.Hir;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A form this comparison takes apart hands over everything it keeps, so what the walk reads of one
 * is the whole of what an equality of it reads.
 *
 * <p>This is the ground the reading of a form stands on. Whether a form's own equality is this
 * comparison is answered part by part, and that is an answer about the form only while the parts are
 * all of it: a part kept back would be read by the equality and by nothing here, and the walk would
 * vouch for a form over the half it could see.
 *
 * <p>A form the walk does <em>not</em> take apart is not this question. Its whole comparison is
 * left to an equality, and whether that answers what this comparison would is said about the form
 * by somebody rather than followed from the walk having stopped — so what such a form keeps is
 * decided where that is said, and not here.
 */
class AFormTheWalkGoesInsideHandsOverEverythingItKeepsTest {

    /** What the comparison is handed. Everything it reaches, it reaches from one of these. */
    private static final List<Class<?>> ROOTS = List.of(
            Hir.Data.class, Hir.SumData.class, Hir.UnitData.class,
            Hir.SpecBehavior.class, Hir.PipeBehavior.class, Hir.FnDef.class);

    @Test
    void everyFormTheWalkGoesInsideHandsOverEverythingItKeeps() {
        Set<Class<?>> goneInside = whereTheWalkGoesThrough();

        assertFalse(goneInside.isEmpty(),
                "a walk that goes inside nothing would pass by reaching nothing to be wrong about");
        for (Class<?> form : goneInside) {
            Set<String> handedOver = new LinkedHashSet<>();
            for (StructuralParts.Part part : StructuralParts.of(form)) {
                handedOver.add(part.name());
            }
            for (Field kept : form.getDeclaredFields()) {
                if (Modifier.isStatic(kept.getModifiers()) || kept.isSynthetic()) {
                    continue;
                }
                assertTrue(handedOver.contains(kept.getName()),
                        form.getName() + " keeps `" + kept.getName() + "` and hands it to nobody,"
                                + " so an equality of it reads what this walk cannot");
            }
        }
    }

    /**
     * The control: a form that kept one back is refused where the parts are read.
     *
     * <p>Without it the sweep above passes by finding nothing whether or not there is anything to
     * find. What refuses it is {@link StructuralParts} itself, which is what makes the sweep a
     * statement about every form rather than about the ones written so far.
     */
    @Test
    void andAFormThatKeptOneBackIsRefusedWhereThePartsAreRead() {
        assertTrue(StructuralParts.areHandedOver(Hir.RetType.class),
                "a written type is one the walk goes inside, which is the shape this stands for");

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> StructuralParts.of(KeepsOneBack.class),
                "a form holding a part it hands to nobody is not one this reads the parts of");
        assertTrue(refused.getMessage().contains("hands it to"),
                "and it says which part, since that is what an author has to move: "
                        + refused.getMessage());
    }

    /**
     * And a form of the grammar that kept one back is refused when it is asked whether it hands its
     * parts over at all.
     *
     * <p>Where the sweep above would otherwise never arrive. Whether parts can be read off a form
     * decides how it is compared, so a form keeping one back is a form nothing can take apart — and
     * for one of the grammar's own kinds that is not an answer but a refusal, the walk going inside
     * those whatever they hold. Asked only where the parts are read, such a form would be passed
     * over as a leaf, the walk would never reach it, and the sweep would go green over it.
     */
    @Test
    void andAFormOfTheGrammarThatKeptOneBackIsRefusedWhenItIsAskedAtAll() {
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> StructuralParts.areHandedOver(AShapeKeepingOneBack.class),
                "a shape a node holds is one the walk goes inside, so keeping a part back is"
                        + " refused rather than making it a form the walk stops at");
        assertTrue(refused.getMessage().contains("hands it to"),
                "and it says which part, as it does where the parts are read: "
                        + refused.getMessage());

        assertFalse(StructuralParts.areHandedOver(KeepsOneBack.class),
                "while the same shape written outside the grammar is a form nothing here takes"
                        + " apart, which is an answer and not a refusal");
    }

    /** Stands for a form that keeps a part behind an equality that would read it. */
    @SuppressWarnings("unused")
    private static final class KeepsOneBack {

        private final String handedOver = "read";

        private final String kept = "unread";

        public String handedOver() {
            return handedOver;
        }
    }

    /** And the same, written as one of the shapes a node of the grammar holds. */
    @SuppressWarnings("unused")
    private static final class AShapeKeepingOneBack implements Hir.Shape {

        private final String handedOver = "read";

        private final String kept = "unread";

        public String handedOver() {
            return handedOver;
        }
    }

    /** The forms the walk goes inside. */
    private static Set<Class<?>> whereTheWalkGoesThrough() {
        Set<Class<?>> through = new LinkedHashSet<>();
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
            through.add(type);
            for (StructuralParts.Part part : StructuralParts.of(type)) {
                todo.addAll(TypesAPartIsDeclaredToHold.named(part.held()));
            }
        }
        return through;
    }
}
