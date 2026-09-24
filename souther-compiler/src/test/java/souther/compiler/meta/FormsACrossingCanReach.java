package souther.compiler.meta;

import souther.compiler.types.BindingId;

import java.lang.reflect.Type;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Every form a value crossing between two builds can meet, worked out from the declarations.
 *
 * <p>The one census, so that a reading of what a crossing depends on and a reading of what a
 * crossing did are held to the same world. Written twice, the second would answer about a smaller
 * one and say nothing about the difference.
 *
 * <p>Where it begins is what a crossing depends on ({@link CrossingProjection}) and not a whole
 * declaration: a declaration holds parts no crossing reads — where it was written, the name it was
 * written under — and a census beginning at one asks for an account of forms no comparison meets.
 *
 * <p>Where it stops is read off the structure, off what the comparison passes over, and off what no
 * published declaration is read back as. Never off how a type was classified: whether something has
 * been decided about is one question and whether there is anything further in it to decide about is
 * another, and a walk steered by the first stops wherever an answer has been written down.
 *
 * <p><b>Which forms there are is settled before what is done with them is asked.</b> A sealed type
 * is not a form — its permitted ones are — so it stands for them whether or not the comparison
 * passes over it. Asked the other way round, an erased sealed type would stop the walk at a name no
 * value ever has, and the forms underneath it would be the ones nobody is asked about.
 */
final class FormsACrossingCanReach {

    private FormsACrossingCanReach() {}

    /**
     * What a crossing depends on, which is where this begins.
     *
     * <p>Read off {@link CrossingProjection} and not off the declarations, so that a part joining
     * what crosses joins this at the same time.
     */
    private static final List<List<CrossingProjection.Taken>> PROJECTION = List.of(
            CrossingProjection.OF_A_PRODUCT, CrossingProjection.OF_A_SUM,
            CrossingProjection.OF_A_UNIT, CrossingProjection.OF_A_DECLARED_BEHAVIOR,
            CrossingProjection.OF_A_PUBLISHED_COMPOSITION, CrossingProjection.OF_A_HELPER);

    /**
     * What a part declared as a primitive arrives as.
     *
     * <p>The comparison is handed values, and a part read off a form by its accessor arrives boxed.
     * A census over declared types that passed a primitive over would leave the form the comparison
     * actually meets reached by nobody — and these are met: a literal holds its number, a set of
     * modifiers holds whether it is partial.
     */
    private static final Map<Class<?>, Class<?>> AS_IT_ARRIVES = Map.of(
            boolean.class, Boolean.class, byte.class, Byte.class, char.class, Character.class,
            short.class, Short.class, int.class, Integer.class, long.class, Long.class,
            float.class, Float.class, double.class, Double.class);

    /** What a part declared as {@code declared} arrives as, boxed where the declaration is a
     *  primitive. Open to the package so every reading over declared types meets the same forms
     *  the comparison does. */
    static Class<?> asItArrives(Class<?> declared) {
        return AS_IT_ARRIVES.getOrDefault(declared, declared);
    }

    /**
     * What the census found: every form a crossing can reach, and the ones it stopped at.
     *
     * @param reached   every form reachable from what a crossing depends on, the leaves among them
     * @param stoppedAt the ones whose parts the census did not go on to
     */
    record Census(Set<Class<?>> reached, Set<Class<?>> stoppedAt) {}

    /**
     * The forms the comparison hands to {@code ConstEval.equal} rather than reading itself.
     *
     * <p>Read off the census and off the comparison's own answers about a form, in the order the
     * comparison takes them: what it passes over, what it has an arm for, and then what it does not
     * take apart. A form reached through none of those is one whose whole comparison is an equality
     * this class did not write.
     *
     * <p>Not the equality of the form. What is delegated to reads a written number by what the
     * language says two written numbers are, so a decimal written two ways is one value here and
     * two to that class's own {@code equals}. The account owed is about the equality that is
     * actually asked, which is why what this is called does not say "its own".
     */
    static Set<Class<?>> handedToADelegatedEquality() {
        Set<Class<?>> handedOver = new LinkedHashSet<>();
        for (Class<?> form : taken().reached()) {
            if (DeclarationAgreement.erases(form) || form.isInterface()
                    || DeclarationAgreement.readByTheAnswerBesideItsSpelling(form)
                    || form == BindingId.class
                    || StructuralParts.areHandedOver(form)) {
                continue;
            }
            handedOver.add(form);
        }
        return handedOver;
    }

    /** The census. */
    static Census taken() {
        Set<Class<?>> seen = new LinkedHashSet<>();
        Deque<Class<?>> todo = new ArrayDeque<>();
        for (List<CrossingProjection.Taken> taken : PROJECTION) {
            for (Type root : CrossingProjection.rootsOf(taken)) {
                todo.addAll(TypesAPartIsDeclaredToHold.named(root));
            }
        }
        Set<Class<?>> reached = new LinkedHashSet<>();
        Set<Class<?>> stoppedAt = new LinkedHashSet<>();
        while (!todo.isEmpty()) {
            Class<?> type = asItArrives(todo.removeFirst());
            if (!seen.add(type)) {
                continue;
            }
            if (type.isSealed()) {
                for (Class<?> permitted : type.getPermittedSubclasses()) {
                    // A form no published declaration is read back as stands for nothing a
                    // crossing meets, and the forms under it are reached by this walk and by no
                    // comparison.
                    if (FormsAPublishedResolutionDoesNotHave.canBeReadBackAs(permitted)) {
                        todo.addLast(permitted);
                    }
                }
                continue;   // the interface itself holds nothing; its forms do
            }
            if (DeclarationAgreement.erases(type)) {
                reached.add(type);
                stoppedAt.add(type);
                continue;   // the comparison does not go inside one, so neither does this
            }
            reached.add(type);
            if (type.isInterface() || !StructuralParts.areHandedOver(type)) {
                stoppedAt.add(type);
                continue;   // a leaf as far as this walk is concerned
            }
            for (StructuralParts.Part part : StructuralParts.of(type)) {
                for (Class<?> held : TypesAPartIsDeclaredToHold.named(part.held())) {
                    todo.addLast(held);
                }
            }
        }
        return new Census(reached, stoppedAt);
    }

}
