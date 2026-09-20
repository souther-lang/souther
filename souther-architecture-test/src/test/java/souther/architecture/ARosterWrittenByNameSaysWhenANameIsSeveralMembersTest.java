package souther.architecture;

import souther.architecture.ARosterWrittenByName.Told;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a roster written by name does with a name several members wear.
 *
 * <p>{@link ARosterWrittenByName} is what lets a rule here write down who does something without
 * writing down what each of them takes, and every rule that uses it is green through it. A hole in
 * it is a hole in all of them at once and none of them can see it, so it is held to subjects of its
 * own: a population and a walk's answers written here, where what each name holds is known.
 *
 * <p>What is checked is the trade the mechanism makes. A name is spelt where a name is one member,
 * which is what makes a rule still under a signature that moved. A name whose members the walk
 * answered differently is refused, which is what a signature was bought for and is the one answer
 * this must not be able to give by accident — so the refusal is asked for here, and asked for on a
 * population where the overloads are the only thing that differs.
 */
class ARosterWrittenByNameSaysWhenANameIsSeveralMembersTest {

    private static final String OWNER = "a/Pass";

    /** A name one member wears, a name two wear, and what each of them takes — a population as a
     *  walk over compiled classes hands one over. */
    private static final Set<String> DECLARED = Set.of(
            OWNER + "#alone(Ljava/lang/String;)V",
            OWNER + "#both(Ljava/lang/String;)V",
            OWNER + "#both(Ljava/lang/String;Ljava/util/List;)V");

    /** Which of the two {@code both} is, said by the parameter that tells them apart. */
    private static final Told THE_ONE_TAKING_A_LIST = Told.takingA(OWNER, "both", 1, List.class);

    /**
     * A name one member wears is spelt as the name, and what it takes is nowhere in the answer.
     *
     * <p>Which is the whole of what this is for: the row a rule writes says who, and a parameter
     * added to that member tomorrow leaves the row where it is.
     */
    @Test
    void aNameOneMemberWearsIsSpeltAsTheName() {
        assertEquals(List.of(OWNER + "#alone"),
                new ARosterWrittenByName(DECLARED, List.of())
                        .namesOf(Set.of(OWNER + "#alone(Ljava/lang/String;)V")),
                "a name nothing else wears is one member, and a row for it has nothing to say"
                        + " about what it takes");
    }

    /**
     * And a name several wear is spelt as the name where the walk answered alike about all of them.
     *
     * <p>An overload beside another is not by itself a reason to say which: what a row would be
     * saying about the rest is what this one says, so the name is one member as far as the rule is
     * concerned.
     */
    @Test
    void andANameSeveralWearIsSpeltAsTheNameWhereTheyWereAnsweredAlike() {
        assertEquals(List.of(OWNER + "#both"),
                new ARosterWrittenByName(DECLARED, List.of()).namesOf(Set.of(
                        OWNER + "#both(Ljava/lang/String;)V",
                        OWNER + "#both(Ljava/lang/String;Ljava/util/List;)V")),
                "every member of this name answered the same, so a row saying the name says about"
                        + " the others what it says about each");
    }

    /**
     * And a name whose members were answered differently is refused.
     *
     * <p>The positive control, and what a signature was bought for. A roster that spelt the name
     * here would be carrying one member's answer under a name the other wears too — which is what
     * an overload added tomorrow would arrive as — so the refusal is what says this mechanism is
     * not simply dropping what a signature said.
     */
    @Test
    void andANameWhoseMembersWereAnsweredDifferentlyIsRefused() {
        AssertionError refused = assertThrows(AssertionError.class,
                () -> new ARosterWrittenByName(DECLARED, List.of())
                        .namesOf(Set.of(OWNER + "#both(Ljava/lang/String;)V")),
                "a name whose members the walk answered differently was written as the name, so"
                        + " one member's answer is being carried under a name another wears");

        assertTrue(refused.getMessage().contains(OWNER + "#both(Ljava/lang/String;)V"),
                "the refusal says a name is short of something without saying which member left"
                        + " it short: " + refused.getMessage());
    }

    /**
     * And told apart, it is spelt by the parameter that tells it apart and nothing else.
     *
     * <p>The parameter and not the signature. What the member answers with and what it takes beside
     * the one named are not here, so the row is as still under a change to either of them as a row
     * that had no overload to contend with.
     */
    @Test
    void andToldApartItIsSpeltByThatParameterAlone() {
        assertEquals(List.of(OWNER + "#both[1=List]"),
                new ARosterWrittenByName(DECLARED, List.of(THE_ONE_TAKING_A_LIST))
                        .namesOf(Set.of(OWNER + "#both(Ljava/lang/String;Ljava/util/List;)V")),
                "the row says which member it is by the parameter that tells it from its sibling");
    }

    /**
     * And a row told apart from the wrong side is refused.
     *
     * <p>The negative control for the one above. A mechanism that spelt whichever member it was
     * handed under whichever row it found first would pass that one while saying nothing, and would
     * go on saying nothing when the two members swapped what they answer.
     */
    @Test
    void andTheOtherMemberOfThatNameIsNotSpeltByThatRow() {
        AssertionError refused = assertThrows(AssertionError.class,
                () -> new ARosterWrittenByName(DECLARED, List.of(THE_ONE_TAKING_A_LIST))
                        .namesOf(Set.of(OWNER + "#both(Ljava/lang/String;)V")),
                "the member that does not take a list was spelt by the row for the one that does");

        assertTrue(refused.getMessage().contains("both"),
                "the refusal does not say which name was short: " + refused.getMessage());
    }

    /**
     * And a row told apart by something its siblings take as well is refused.
     *
     * <p>The way a row could go on saying one member's answer about another through the very thing
     * that was meant to stop it. Both members of {@code both} take a string first, so a row saying
     * so picks out neither of them, and the two would be written under one spelling with whichever
     * the walk answered last standing for the pair.
     */
    @Test
    void andARowToldApartByWhatItsSiblingsTakeTooIsRefused() {
        Told shared = Told.takingA(OWNER, "both", 0, String.class);

        AssertionError refused = assertThrows(AssertionError.class,
                () -> new ARosterWrittenByName(DECLARED, List.of(shared))
                        .namesOf(Set.of(OWNER + "#both(Ljava/lang/String;)V")),
                "a row picking out both members of a name was taken for one that says which");

        assertTrue(refused.getMessage().contains(shared.spelt()),
                "the refusal does not say which row picks out several: " + refused.getMessage());
    }

    /**
     * And a member two rows both pick out is refused.
     *
     * <p>The other way round from the one above, and the way a roster settles a member by the order
     * somebody wrote its rows in. Reading the rows until one matches, the member is spelt as
     * whichever of them came first — so two claims about one member are resolved by the list's
     * order, and the spelling moves the first time somebody reorders it.
     *
     * <p>Both rows pick one member each here, so nothing about either of them on its own says
     * anything is wrong.
     */
    @Test
    void andAMemberTwoRowsBothPickOutIsRefused() {
        Set<String> declared = Set.of(
                OWNER + "#both(Ljava/lang/String;Ljava/lang/Integer;)V",
                OWNER + "#both(Ljava/lang/Object;Ljava/lang/Long;)V");
        List<Told> bothPickingTheFirst = List.of(
                Told.takingA(OWNER, "both", 0, String.class),
                Told.takingA(OWNER, "both", 1, Integer.class));

        AssertionError refused = assertThrows(AssertionError.class,
                () -> new ARosterWrittenByName(declared, bothPickingTheFirst)
                        .namesOf(Set.of(OWNER + "#both(Ljava/lang/String;Ljava/lang/Integer;)V")),
                "one member was picked out by two rows and written as whichever came first");

        assertTrue(refused.getMessage().contains("String") && refused.getMessage().contains("Integer"),
                "the refusal does not name the rows that both pick it: " + refused.getMessage());
    }

    /**
     * And the refusal names every member it is short of, and not the first of them.
     *
     * <p>Saying which member a row means is one edit each, and a roster is short of however many it
     * is short of. Refused on the first, a rule would be read as one edit from green and would find
     * the next one every time somebody made that edit.
     */
    @Test
    void andTheRefusalNamesEveryMemberItIsShortOf() {
        Set<String> declared = Set.of(
                OWNER + "#both(Ljava/lang/String;)V",
                OWNER + "#both(Ljava/lang/String;Ljava/util/List;)V",
                OWNER + "#other(Ljava/lang/String;)V",
                OWNER + "#other(Ljava/lang/String;Ljava/util/List;)V");

        AssertionError refused = assertThrows(AssertionError.class,
                () -> new ARosterWrittenByName(declared, List.of()).namesOf(Set.of(
                        OWNER + "#both(Ljava/lang/String;)V",
                        OWNER + "#other(Ljava/lang/String;)V")));

        assertTrue(refused.getMessage().contains("#both(") && refused.getMessage().contains("#other("),
                "the refusal names one of the two members nothing tells apart: "
                        + refused.getMessage());
    }

    /**
     * And what a walk answered is carried over to the name it is written under.
     *
     * <p>{@link ARosterWrittenByName#by} is asked for rules whose answer is more than whether, and
     * what it must not do is lose the answer on the way to the name. A collapse that handed back
     * the names alone would leave a rule counting nothing and reading as though it had counted.
     */
    @Test
    void andWhatTheWalkAnsweredIsCarriedToTheNameItIsWrittenUnder() {
        assertEquals(Map.of(OWNER + "#alone", 3),
                new ARosterWrittenByName(DECLARED, List.of())
                        .by(Map.of(OWNER + "#alone(Ljava/lang/String;)V", 3)),
                "the answer the walk gave this member is what the row it is written under holds");
    }

    /**
     * And a member of no population is refused.
     *
     * <p>Whether a name is one member is read off the population, so a member that is not in one is
     * a question this cannot answer. Spelt as its name regardless, it would be written down as one
     * member on the strength of a population that never held it.
     */
    @Test
    void andAMemberOfNoPopulationIsRefused() {
        assertThrows(AssertionError.class,
                () -> new ARosterWrittenByName(DECLARED, List.of())
                        .namesOf(Set.of(OWNER + "#neverDeclared()V")),
                "a member the population does not hold was spelt as though its name had been"
                        + " looked up in one");
    }
}
