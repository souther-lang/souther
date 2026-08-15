package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Ast;

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

/**
 * Every form a published declaration is made of is one {@link DeclarationAgreement} has decided
 * about.
 *
 * <p>The comparison walks declarations as the forms they are, so a form the language gains is
 * compared by whatever it does next — and what it does next is not a decision anyone made. This is
 * where the decision is required: a type reached from a declaration is a record and is compared part
 * by part, or it is a value the comparison names, or it is erased because where something is written
 * is not something a value can be read differently by. A fourth is what this refuses to let exist.
 *
 * <p>Static, over what a declaration can reach rather than over what some test happened to build. A
 * form added to a corner of the grammar no fixture writes would otherwise sit there until the day an
 * author used it, and be answered about then by nobody.
 *
 * <p>The failure is not "add it to the list". It is a question with two answers, and which one is
 * right is a fact about the new form: does what a value crossing between two builds is read by depend
 * on it? An operand of an invariant does, a field's type does, a marker saying which pass rewrote a
 * node does not.
 */
class EveryFormADeclarationIsMadeOfIsClassifiedTest {

    /** What the comparison is handed: a declaration, a behavior's signature, a published helper, and
     *  an import's binding. Everything it reaches, it reaches from one of these. */
    private static final List<Class<?>> ROOTS = List.of(
            Ast.Data.class, Ast.SumData.class, Ast.UnitData.class,
            Ast.SpecBehavior.class, Ast.PipeBehavior.class,
            Ast.FnDef.class, Ast.Import.class);

    @Test
    void everyTypeADeclarationReachesIsRecordValueOrErased() {
        Set<Class<?>> reached = reachableFromDeclarations();

        assertFalse(reached.isEmpty(), "a walk that reaches nothing would pass for any reason");
        List<String> undecided = new ArrayList<>(new TreeSet<>(
                reached.stream().filter(t -> !decided(t)).map(Class::getName).toList()));
        assertEquals(List.of(), undecided,
                "a declaration is made of these and the comparison has not decided about them."
                        + " Each is compared as a value, or erased because a value cannot be read"
                        + " differently by it");
    }

    /** The control: the walk can tell an undecided type from a decided one. */
    @Test
    void andTheWalkWouldSeeAnUndecidedTypeIfThereWereOne() {
        assertFalse(decided(java.util.UUID.class),
                "a type nothing here classifies is not passed over");
        assertFalse(DeclarationAgreement.isAFormOfTheGrammar(
                        souther.compiler.types.BindingId.class),
                "a record from outside the grammar is not a form of a declaration by being one");
    }

    /** Whether {@code type} is one the comparison has an answer for. */
    private static boolean decided(Class<?> type) {
        return DeclarationAgreement.isAFormOfTheGrammar(type) || erased(type)
                || DeclarationAgreement.comparedAsAValue(type);
    }

    /** Whether the comparison erases it — where something is written, and nothing else. */
    private static boolean erased(Class<?> type) {
        return DeclarationAgreement.erases(type);
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
            if (erased(type)) {
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
