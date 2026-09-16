package souther.compiler.meta;

import souther.compiler.ast.Hir;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Every form a published declaration reaches, whatever a crossing does with it.
 *
 * <p>Not {@link FormsACrossingCanReach}, and the difference is the question. That one is over what a
 * value crossing between two builds depends on: it begins at the parts a crossing reads and stops
 * where no published declaration is read back as the form. This one is over what a declaration is
 * made of, which is asked whether or not anything looks at it — a form says what it is before
 * anybody has decided what to do with one.
 *
 * <p>So a form a crossing never meets is still a form, and is still to say which of the three
 * things it is. Answered off the crossing's census instead, the account for one would go missing the
 * day a crossing stopped reaching it, and what it is would have been decided by what is done with
 * it — which is the arrangement the reading of these forms was written against.
 */
final class FormsADeclarationReaches {

    private FormsADeclarationReaches() {}

    /** What the comparison is handed: a declaration, a behavior's signature, a published helper.
     *  Everything a declaration holds, it holds under one of these. */
    private static final List<Class<?>> ROOTS = List.of(
            Hir.Data.class, Hir.SumData.class, Hir.UnitData.class,
            Hir.SpecBehavior.class, Hir.PipeBehavior.class, Hir.FnDef.class);

    /**
     * Every form reachable from a declaration, through the parts a form hands over and the
     * containers they are held in. A sealed type stands for its permitted forms.
     *
     * <p>Where it stops is read off the structure and off what the comparison passes over, and never
     * off how a type was classified. Those are two questions: whether something has been decided
     * about is one, and whether there is anything further in it to decide about is the other. A walk
     * steered by the classification stops wherever an answer has been written down, so a form under
     * one is reached by nobody and decided by nobody.
     */
    static Set<Class<?>> reached() {
        Set<Class<?>> seen = new LinkedHashSet<>();
        Deque<Class<?>> todo = new ArrayDeque<>(ROOTS);
        Set<Class<?>> reached = new LinkedHashSet<>();
        while (!todo.isEmpty()) {
            Class<?> type = todo.removeFirst();
            if (!seen.add(type) || type.isPrimitive()) {
                continue;
            }
            if (type.isSealed()) {
                for (Class<?> permitted : type.getPermittedSubclasses()) {
                    todo.addLast(permitted);
                }
                continue;   // the interface itself holds nothing; its forms do
            }
            reached.add(type);
            if (DeclarationAgreement.erases(type) || type.isInterface()
                    || !StructuralParts.areHandedOver(type)) {
                continue;   // a leaf as far as this walk is concerned
            }
            for (StructuralParts.Part part : StructuralParts.of(type)) {
                for (Class<?> held : TypesAPartIsDeclaredToHold.named(part.held())) {
                    todo.addLast(held);
                }
            }
        }
        return reached;
    }

}
