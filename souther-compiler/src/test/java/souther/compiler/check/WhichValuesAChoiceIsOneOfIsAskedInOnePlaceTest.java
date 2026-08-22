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

    /** The arms of {@code Core} that answer one of several values. */
    private static final Set<String> ANSWER_ONE_OF_SEVERAL =
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
        Set<String> named = new LinkedHashSet<>(ANSWER_ONE_OF_SEVERAL);
        named.removeAll(arms);
        assertEquals(Set.of(), named,
                "a node named here is not an arm of Core, so this rule is about something the"
                        + " language no longer has");

        Set<String> unclassified = new LinkedHashSet<>(arms);
        unclassified.removeAll(ANSWER_ONE_OF_SEVERAL);
        unclassified.removeAll(ANSWERS_ONE_VALUE);
        assertEquals(Set.of(), unclassified,
                "Core has an arm nobody has said answers one of several or answers one value."
                        + " Decide which: a choice goes in ANSWER_ONE_OF_SEVERAL and into Choice.of,"
                        + " and anything else goes in ANSWERS_ONE_VALUE. Defaulting it silently is"
                        + " how an attempted construction went unread");
    }

    /** And a node that answers one value is not a choice, so a reader asks rather than knowing which
     * nodes to ask about. */
    @Test
    void nothingIsNoChoice() {
        assertNull(Choice.of(null), "nothing is not a value that is one of several");
    }

    /**
     * The arms of {@code Core} that answer one value. Written out beside the choices so that the two
     * together are every arm there is, which is what makes the check above a tripwire rather than a
     * list of what someone happened to think of.
     *
     * <p>{@code PreservedCall} is here as a node and not as every call. What a call answers is one
     * value unless the operation is defined in cases — {@code Int.min} answers one of the two it was
     * given — and which operations those are is a table rather than a shape
     * ({@code DischargeRules.CHOOSES}). So a call is not a choice by being a call, and the day that
     * table is read here it is {@link Choice} that grows a case rather than this list (#974).
     *
     * <p>{@code Unreachable} answers no value at all, which is not answering one of several.
     */
    private static final Set<String> ANSWERS_ONE_VALUE = Set.of(
            "Int", "Decimal", "Str", "Bool", "Temporal", "Read", "UnitValue", "Neg", "FieldAccess",
            "Binary", "Call", "PreservedCall", "Apply", "LetIn", "Block", "ListLit", "OptionSome",
            "OptionNone", "Tuple", "TupleGet", "Construct", "Unreachable");
}
