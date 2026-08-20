package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;

import java.lang.reflect.ParameterizedType;
import java.lang.reflect.RecordComponent;
import java.lang.reflect.Type;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every record a published declaration is made of is one {@link DeclarationAgreement} has decided
 * about.
 *
 * <p>The comparison walks a form's components when it has nothing else to say about it, which is
 * right for a form of the grammar and is a default for everything else. A record the compiler puts
 * beside a declaration to say something about itself — which pass rewrote a node, what a coverage
 * point was numbered as — joins the comparison the day it is added, and two builds that mean the
 * same thing start disagreeing over it. Nothing says so: the language still compiles, every test
 * still passes, and what changed is what two builds are held to.
 *
 * <p>So the walk is required to be a decision. A record reachable from a declaration is a form of
 * the grammar, or it is one the comparison names and says how to hold, or it is erased because a
 * value cannot be read differently by it. There is no fourth, and this is what refuses one.
 *
 * <p>Static, over what a declaration can reach rather than over what some fixture happened to build.
 * A form in a corner of the grammar no test writes would otherwise sit there until an author used
 * it, and be answered about then by nobody.
 */
class EveryFormADeclarationIsMadeOfIsClassifiedTest {

    /** What the comparison is handed: a declaration, a behavior's signature, a published helper.
     *  Everything it reaches, it reaches from one of these. */
    private static final List<Class<?>> ROOTS = List.of(
            Hir.Data.class, Hir.SumData.class, Hir.UnitData.class,
            Hir.SpecBehavior.class, Hir.PipeBehavior.class, Hir.FnDef.class);

    @Test
    void everyRecordADeclarationReachesIsAFormOrNamedOrErased() {
        Set<Class<?>> reached = reachableFromDeclarations();

        assertFalse(reached.isEmpty(), "a walk that reaches nothing would pass for any reason");
        List<String> undecided = new ArrayList<>(new TreeSet<>(reached.stream()
                .filter(Class::isRecord).filter(t -> !decided(t)).map(Class::getName).toList()));

        assertEquals(List.of(), undecided,
                "a declaration is made of these and the comparison has not decided about them."
                        + " Each is a form of the grammar, or one the comparison names, or erased"
                        + " because a value crossing between two builds cannot be read differently"
                        + " by it");
    }

    /**
     * The control: the walk can tell an undecided record from a decided one.
     *
     * <p>Without it, a walk that reached nothing but forms of the grammar — or one whose predicate
     * answered yes to everything — would pass while saying nothing.
     */
    @Test
    void andTheWalkWouldSeeAnUndecidedRecordIfThereWereOne() {
        assertFalse(decided(Undecided.class),
                "a record nothing here classifies is not passed over");
        assertFalse(DeclarationAgreement.isAFormOfTheGrammar(
                        souther.compiler.types.BindingId.class),
                "a record from outside the grammar is not a form of a declaration by being one");
        assertTrue(DeclarationAgreement.namedByTheComparison(
                        souther.compiler.types.BindingId.class),
                "it is decided by being named, which is the other way of deciding");
    }

    /** Stands for a record someone adds to a declaration without saying what it is. */
    private record Undecided(String what) {}

    /** Whether {@code type} is one the comparison has an answer for. */
    private static boolean decided(Class<?> type) {
        return DeclarationAgreement.isAFormOfTheGrammar(type)
                || DeclarationAgreement.isASettledAnswer(type)
                || DeclarationAgreement.namedByTheComparison(type)
                || DeclarationAgreement.erases(type);
    }

    /** Every type reachable from a published declaration, through record components and the
     *  containers they are held in. A sealed type stands for its permitted forms. */
    private static Set<Class<?>> reachableFromDeclarations() {
        Set<Class<?>> seen = new LinkedHashSet<>();
        Deque<Class<?>> todo = new ArrayDeque<>(ROOTS);
        Set<Class<?>> reached = new LinkedHashSet<>();
        while (!todo.isEmpty()) {
            Class<?> type = todo.removeFirst();
            if (!seen.add(type) || type.isPrimitive()) {
                continue;
            }
            if (DeclarationAgreement.erases(type)
                    || DeclarationAgreement.namedByTheComparison(type)) {
                reached.add(type);
                continue;   // the comparison does not go inside one, so neither does this
            }
            if (type.isSealed()) {
                for (Class<?> permitted : type.getPermittedSubclasses()) {
                    todo.addLast(permitted);
                }
                continue;   // the interface itself holds nothing; its forms do
            }
            if (type.isInterface() || !type.isRecord()) {
                reached.add(type);
                continue;   // a leaf as far as this walk is concerned
            }
            reached.add(type);
            for (RecordComponent part : type.getRecordComponents()) {
                for (Class<?> held : held(part.getGenericType())) {
                    todo.addLast(held);
                }
            }
        }
        return reached;
    }

    /** The types a component holds: itself, or what its container is of. */
    private static List<Class<?>> held(Type type) {
        if (type instanceof Class<?> plain) {
            return plain.isArray() ? List.of(plain.getComponentType()) : List.of(plain);
        }
        if (type instanceof ParameterizedType parameterized
                && parameterized.getRawType() instanceof Class<?> raw
                && (raw == List.class || raw == Set.class || raw == Optional.class
                        || raw == Map.class)) {
            List<Class<?>> of = new ArrayList<>();
            for (Type argument : parameterized.getActualTypeArguments()) {
                of.addAll(held(argument));
            }
            return of;
        }
        return List.of();   // a wildcard or a type variable holds nothing this walk can name
    }
}
