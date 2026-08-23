package souther.compiler.check;

import souther.compiler.core.Core;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Modifier;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Which values a choice is one of is asked in one place, and a node of {@link Core} that answers one
 * of several is not left out of it.
 *
 * <p>It was asked in four places and each wrote its own list — the search for a split in a value
 * position, the reading of what a split's arms are, the test of whether a node is one, and the
 * recording of what a value was computed from. All four said {@code if} and {@code match}, and none
 * said an attempted construction, which answers what it built where its invariant held and what it
 * departs with where it did not. So an attempt was a value with a name and nothing recorded about
 * the values it is one of, which is what {@link Derivation.Chosen} was made for, standing under a
 * third spelling and reached by none of the readers that were fixed.
 *
 * <p>What a node answers is a judgement and not something reflection decides — a record with two
 * {@code Core} components may be arithmetic over both or one of either — so the judgement is written
 * out below. What is held here is that writing it out cannot be how a node goes missing: the names
 * are matched against {@code Core}'s own arms, so an arm added or renamed stops this until someone
 * has said which it is.
 */
class WhichValuesAChoiceIsOneOfIsAskedInOnePlaceTest {

    /** The arms of {@code Core} that are a choice by their shape — the ones {@link Choice} answers
     * for whatever stands in them. Named against its opposite: what a shape can say is whether every
     * value written at that node is one of several, and for a call it cannot, so a call is on the
     * other side and is answered for by what its operation is rather than by what it is. */
    private static final Set<String> A_CHOICE_BY_ITS_SHAPE =
            Set.of("If", "Match", "IfConstructed");

    /** Every arm {@code Core} declares. */
    private static Set<String> coreArms() {
        Class<?>[] arms = Core.class.getPermittedSubclasses();
        assertNotNull(arms, "Core is a sum, and this reads its arms rather than a list of them");
        return Arrays.stream(arms)
                .filter(c -> !Modifier.isAbstract(c.getModifiers()))
                .map(Class::getSimpleName)
                .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new));
    }

    /**
     * Every node named as answering one of several is an arm of {@code Core}, and every arm is
     * classified.
     *
     * <p>The second half is the tripwire. A node added to the language answers one of several or it
     * does not, and which it is decides whether a value written at it has a range — so the day one
     * arrives, this stops rather than defaulting it to "not a choice" and losing the reading again.
     */
    @Test
    void everyArmOfCoreIsClassifiedAndTheChoicesAreAmongThem() {
        Set<String> arms = coreArms();
        Set<String> named = new LinkedHashSet<>(A_CHOICE_BY_ITS_SHAPE);
        named.removeAll(arms);
        assertEquals(Set.of(), named,
                "a node named here is not an arm of Core, so this rule is about something the"
                        + " language no longer has");

        Set<String> unclassified = new LinkedHashSet<>(arms);
        unclassified.removeAll(A_CHOICE_BY_ITS_SHAPE);
        unclassified.removeAll(NOT_A_CHOICE_BY_ITS_SHAPE);
        assertEquals(Set.of(), unclassified,
                "Core has an arm nobody has classified."
                        + " Decide which: a choice goes in A_CHOICE_BY_ITS_SHAPE and into Choice.of,"
                        + " and anything else goes in NOT_A_CHOICE_BY_ITS_SHAPE. Defaulting it"
                        + " silently is how an attempted construction went unread");
    }

    /** And a reader asks rather than knowing which nodes to ask about. */
    @Test
    void nothingIsNoChoice() {
        assertNull(Choice.of(null), "nothing is not a value that is one of several");
    }

    /**
     * The arms of {@code Core} that are not a choice by their shape. Written out beside the choices
     * so that the two together are every arm there is, which is what makes the check above a
     * tripwire rather than a list of what someone happened to think of.
     *
     * <p>Named for what it is and not for what its members answer, which is not one thing.
     * {@code Unreachable} answers no value at all and {@code Block} answers none of its own — being
     * a closure, read where it is applied — and neither is answering one of several.
     *
     * <p>{@code PreservedCall} is here as a shape and not as every call. What a call answers is one
     * value unless the operation is defined in cases — {@code Int.min} answers one of the two it was
     * given — and which operations those are is a table rather than a shape
     * ({@code DischargeRules.CHOOSES}). That table is read in {@link Choice} and this row stays where
     * it is: a call is not a choice by being a call, so a shape cannot put it on the other side, and
     * a check that moved it there would be claiming of every call what is true of six operations. A
     * classification by shape is what this list can hold; which values a particular call answers one
     * of is {@link Choice}'s, as it is for every other node here.
     */
    private static final Set<String> NOT_A_CHOICE_BY_ITS_SHAPE = Set.of(
            "Int", "Decimal", "Str", "Bool", "Temporal", "Read", "UnitValue", "Neg", "FieldAccess",
            "Binary", "Call", "PreservedCall", "Apply", "LetIn", "Block", "ListLit", "OptionSome",
            "OptionNone", "Tuple", "TupleGet", "Construct", "Unreachable");
}
