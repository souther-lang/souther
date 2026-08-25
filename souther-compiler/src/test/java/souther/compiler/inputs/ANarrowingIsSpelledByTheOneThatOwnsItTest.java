package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.types.TypeSymbol;

import java.lang.reflect.Constructor;
import java.lang.reflect.Modifier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A narrowing is spelled where narrowings are owned, and nowhere else.
 *
 * <p>Measured against the shape of the API rather than against an answer. {@link Refinement#of} says
 * it is "the one place the two vocabularies are related", and {@code TermPath.requirements} says a
 * requirement is read from the path "here and nowhere else" — both sentences, and both were kept by
 * whoever happened to read them. The classes of a position spelled a sum's narrowing a second time
 * and never spelled an optional's, so an optional's classes narrowed nothing and two of them could
 * sit in one row; and the boundary search planned a value against no requirement at all, so a row
 * offered for a line under a case carried another case. A sentence is kept by whoever reads it; a
 * signature is kept by everyone (ADR-0114).
 *
 * <p>The scan below is a tripwire under that, not the other way round — what holds it is that the
 * variants have no constructor a caller can reach.
 */
class ANarrowingIsSpelledByTheOneThatOwnsItTest {

    @Test
    void aNarrowingHasNoConstructorAReaderCanReach() {
        for (Class<?> variant : new Class<?>[] {Refinement.SumCase.class, Refinement.Presence.class}) {
            for (Constructor<?> each : variant.getDeclaredConstructors()) {
                assertTrue(Modifier.isPrivate(each.getModifiers()),
                        "a reader could spell a narrowing of its own: " + each);
            }
            assertEquals(0, variant.getConstructors().length,
                    () -> "and none of " + variant.getSimpleName()
                            + " is reachable by reflection either");
        }
    }

    /**
     * And the two ways in take what they are named for.
     *
     * <p>Written out rather than counted. {@link Refinement#of} answers which narrowing a
     * distinction is, and {@link Refinement#sumCase} builds one for a caller that already has the
     * case — two questions, and a third entry arriving is a decision somebody made here.
     */
    @Test
    void everyWayInTakesWhatTheNarrowingIsReadFrom() {
        assertEquals(Refinement.sumCase(TypeSymbol.primitive("Int")),
                Refinement.of(new Case.SumCase(TypeSymbol.primitive("Int"), false)),
                "one case read two ways is one narrowing");
        assertEquals(2, java.util.Arrays.stream(Refinement.class.getDeclaredMethods())
                        .filter(each -> Modifier.isStatic(each.getModifiers()))
                        .count(),
                "a third way to spell a narrowing is a decision, not an accident: "
                        + java.util.Arrays.toString(Refinement.class.getDeclaredMethods()));
    }

    /**
     * A narrowing is what it narrows to, and not which object it is.
     *
     * <p>Load-bearing rather than tidy. Every reader deciding whether two requirements hold together
     * does it by equality ({@link Requirements#merge}), and every branch of a position is found by
     * comparing the narrowing it carries — so an identity comparison would have no two narrowings
     * ever agree, which reads as a model whose cases are all incompatible.
     */
    @Test
    void twoNarrowingsToTheSameThingAreOne() {
        assertEquals(Refinement.sumCase(TypeSymbol.primitive("Int")),
                Refinement.sumCase(TypeSymbol.primitive("Int")));
        assertEquals(Refinement.sumCase(TypeSymbol.primitive("Int")).hashCode(),
                Refinement.sumCase(TypeSymbol.primitive("Int")).hashCode());
        assertNotEquals(Refinement.sumCase(TypeSymbol.primitive("Int")),
                Refinement.sumCase(TypeSymbol.primitive("Bool")));

        assertEquals(Refinement.of(new Case.Presence(true)), Refinement.of(new Case.Presence(true)));
        assertNotEquals(Refinement.of(new Case.Presence(true)),
                Refinement.of(new Case.Presence(false)));
        assertFalse(Refinement.of(new Case.Presence(true))
                        .equals(Refinement.sumCase(TypeSymbol.primitive("Int"))),
                "and a presence is not a case of a sum");
    }
}
