package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclaredSig;
import souther.compiler.check.Emptiness;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An input is proved to have no value only where its rules leave it none, and the proof says where.
 *
 * <p>The cases of a sum are a choice. A sum has a value wherever any of its cases does, so what
 * proves it has none is every case at once. Read as a conjunction — every case's rules met into one
 * space — a model with one refused case comes back as a behavior that takes nothing, and every
 * comparison written about it is answered {@code NoFeasibleInput} while the rows a reader is owed are
 * rows an author can write. A case this reading never entered is not one of the cases that prove
 * anything: nothing was shown about it, which is not the same as its having been shown to hold
 * nothing.
 *
 * <p>A sequence is read with the same asymmetry. A container that may hold none is a value whatever
 * is true of what it would hold; where a rule says it holds at least one, an element nothing can
 * build leaves the input nothing, and the proof says which of the two facts it took.
 *
 * <p>Two structures a value has at once are the other fold. Over two structures a row has both of,
 * one that is impossible is the whole answer, so a sum this reading never finished with does not hide
 * what the structure beside it proved, whichever order the fields are declared in.
 *
 * <p>And a name the cases of a sum share is one subject in every language the rules are read in.
 * What the value above says about it and what the case says about it are about the same thing,
 * whether what they say is a bound on an order or which values may stand there; carried as two
 * subjects, the two clauses would never meet and every answer would be wider rather than wrong.
 * {@link ARelationOverSharedNamesReachesTheNumbersTheyStandAtTest} measures the same crossing where
 * the rules are arithmetic.
 */
class AnInputIsEmptyOnlyWhereTheRulesLeaveItNothingTest {

    private static final String EVERY_CASE_REFUSED = """
            module g

            data A = { x: Int }
                invariant impossible = x >= 1 && x <= 0
            data B = { y: Int }
                invariant impossible = y >= 1 && y <= 0
            data Q = A | B

            data Holder = { q: Q }

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    /**
     * The same, with one case left standing, so that what refuses the input is the whole list.
     *
     * <p>The case whose rules refuse it stands under its narrowing whether or not a name crosses it:
     * {@code A} and {@code B} share nothing here, and {@code A}'s rules still hold only of the rows
     * where {@code q} is an {@code A}.
     */
    private static final String ONE_CASE_STANDS =
            EVERY_CASE_REFUSED.replace("    invariant impossible = y >= 1 && y <= 0\n", "");

    /**
     * A sum whose cases the reading never enters, because the walk turns back where a path returns
     * to a declaration already open on it.
     */
    private static final String NEVER_ENTERED = """
            module g

            data Leaf = { n: Int }
                invariant impossible = n >= 1 && n <= 0
            data Node = { left: Tree, right: Tree }
            data Tree = Leaf | Node

            data Holder = { tree: Tree }

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    /** One case refused by its own rules, beside a case with the same shared fields. */
    private static final String DEAD_CASE = """
            module g

            data Shared = { lo: Int, hi: Int }
            data A = { ...Shared, x: Int }
                invariant impossible = x >= 1 && x <= 0
            data B = { ...Shared, y: Int }
            data Q = A | B

            data Holder = { q: Q }

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    /**
     * The same, with the case refused by its own rules together with the rule the record wrote.
     *
     * <p>Neither {@code lo >= 10} nor {@code hi <= 5} refuses {@code A} on its own, and the record's
     * {@code lo <= hi} refuses nothing until it is read at the numbers the names stand at. So this
     * is a case that is empty only once the relation is carried, and it is the model that says the
     * carry and the choice are one change: carried into a conjunction of the cases, this refuses the
     * whole input.
     */
    private static final String DEAD_ONCE_THE_RELATION_IS_CARRIED = """
            module g

            data Shared = { lo: Int, hi: Int }
            data A = { ...Shared, x: Int }
                invariant low = lo >= 10
                invariant high = hi <= 5
            data B = { ...Shared, y: Int }
            data Q = A | B

            data Holder = { q: Q }
                invariant ordered = q.lo <= q.hi

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    /**
     * A sequence inside a case, of an element the rules refuse, that the case says holds something.
     *
     * <p>Both conditions at once: the element's rules are about the rows where {@code q} is an
     * {@code A} and where the list holds something, and neither of those is every row. So {@code A}
     * has no value and {@code B} is untouched.
     */
    private static final String A_SEQUENCE_INSIDE_A_CASE = """
            module g

            data Item = { charge: Int }
                invariant impossible = charge >= 1 && charge <= 0
            data A = { items: List<Item> }
                invariant atLeastOne = List.length(items) >= 1
            data B = { y: Int }
            data Q = A | B

            data Holder = { q: Q }

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    /** A sum inside a sequence, one case of which the rules refuse. */
    private static final String A_CASE_INSIDE_A_SEQUENCE = """
            module g

            data A = { x: Int }
                invariant impossible = x >= 1 && x <= 0
            data B = { y: Int }
            data Q = A | B

            data Item = { q: Q }
            data Holder = { items: List<Item> }
                invariant atLeastOne = List.length(items) >= 1

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    /** A sequence of an element there is no value of, which nothing says holds anything. */
    private static final String MAY_BE_EMPTY = """
            module g

            data Item = { charge: Int }
                invariant impossible = charge >= 1 && charge <= 0
            data Holder = { items: List<Item> }

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    /** The same, with the container told to hold something. */
    private static final String HOLDS_AT_LEAST_ONE = MAY_BE_EMPTY.replace(
            "data Holder = { items: List<Item> }",
            """
                    data Holder = { items: List<Item> }
                        invariant atLeastOne = List.length(items) >= 1""");

    /** And the same again with an element there is a value of, so that what refuses the input is
     *  the pair and not the rule about the length. */
    private static final String AND_AN_ELEMENT_THAT_STANDS =
            HOLDS_AT_LEAST_ONE.replace("    invariant impossible = charge >= 1 && charge <= 0\n",
                    "");

    /**
     * A sum this walk turns back at, beside one whose every case the rules refuse.
     *
     * <p>{@code Tree} is read as far as it goes and no further, so nothing is known about the sums
     * under it. {@code Q} is known: neither of its cases has a value, so no value of the input has
     * one either — whatever is or is not known about the tree beside it.
     */
    private static final String UNREAD_BESIDE_REFUSED = """
            module g

            data Leaf = { n: Int }
            data Node = { left: Tree, right: Tree }
            data Tree = Leaf | Node

            data A = { x: Int }
                invariant impossible = x >= 1 && x <= 0
            data B = { y: Int }
                invariant impossible = y >= 1 && y <= 0
            data Q = A | B

            data Holder = { tree: Tree, q: Q }

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    /** The same two fields, declared the other way round. */
    private static final String REFUSED_BESIDE_UNREAD =
            UNREAD_BESIDE_REFUSED.replace("data Holder = { tree: Tree, q: Q }",
                    "data Holder = { q: Q, tree: Tree }");

    /** A sequence that cannot be empty, of an element there is no value of, beside the same
     *  unfinished tree. */
    private static final String UNREAD_BESIDE_A_DEAD_ELEMENT = """
            module g

            data Leaf = { n: Int }
            data Node = { left: Tree, right: Tree }
            data Tree = Leaf | Node

            data Item = { charge: Int }
                invariant impossible = charge >= 1 && charge <= 0

            data Holder = { tree: Tree, items: List<Item> }
                invariant atLeastOne = List.length(items) >= 1

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    /**
     * A bound on an order, said above and said in every case, that no value meets.
     *
     * <p>Neither clause refuses anything on its own. Read as one subject they leave the name
     * nothing, and every case of the sum is a case no value stands at.
     */
    private static final String ON_AN_ORDER = """
            module g

            data Shared = { tag: String }
            data A = { ...Shared, x: Int }
                invariant late = tag >= "M"
            data B = { ...Shared, y: Int }
                invariant late = tag >= "M"
            data Q = A | B

            data Holder = { q: Q }
                invariant early = q.tag <= "A"

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    /** The same model with the rule the value above wrote taken out. */
    private static final String ON_AN_ORDER_UNRULED =
            ON_AN_ORDER.replace("    invariant early = q.tag <= \"A\"\n", "");

    /**
     * Which values may stand at the name, said above and said in every case.
     *
     * <p>An equality is a set of one and an exclusion is that set taken away, and neither is a range
     * — so this is the reading that answers where the order and the arithmetic have nothing to say.
     */
    private static final String ON_THE_VALUES = """
            module g

            data Shared = { tag: String }
            data A = { ...Shared, x: Int }
                invariant notThat = tag /= "A"
            data B = { ...Shared, y: Int }
                invariant notThat = tag /= "A"
            data Q = A | B

            data Holder = { q: Q }
                invariant thatOne = q.tag == "A"

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    private static final String ON_THE_VALUES_UNRULED =
            ON_THE_VALUES.replace("    invariant thatOne = q.tag == \"A\"\n", "");

    @Test
    void everyCaseRefusedLeavesTheInputNone() {
        Optional<EmptyInput> why = emptinessOf(EVERY_CASE_REFUSED);

        assertTrue(why.isPresent(), "no value of Q is left, so no value of the input is");
        Emptiness proof = ((EmptyInput.ProvedByTheRules) why.orElseThrow()).why();
        Emptiness.AtAField at = assertInstanceOf(Emptiness.AtAField.class, proof,
                "the lack is at the sum, which is the place a reader is sent to");
        assertEquals(new Emptiness.AtAField.Where.In("h.q"), at.where());
        assertEquals(2, assertInstanceOf(Emptiness.AcrossEveryCase.class, at.under(),
                "and it is proved over every case rather than by one of them").cases().size());
    }

    @Test
    void andOneStandingCaseIsEnoughToLeaveIt() {
        assertEquals(Optional.empty(), emptinessOf(ONE_CASE_STANDS),
                "every B is a row this behavior takes");
    }

    /**
     * A case this reading did not enter proves nothing.
     *
     * <p>The walk stops where a path returns to a declaration already open on it, so the sums under
     * {@code Node} are met and never read. Read as cases that hold nothing, the recursion itself
     * would refuse every model that has one.
     */
    @Test
    void aCaseThisReadingDidNotEnterProvesNothing() {
        assertEquals(Optional.empty(), emptinessOf(NEVER_ENTERED),
                "a tree of one node is a row this behavior takes, and the deeper sums were never"
                        + " read");
    }

    @Test
    void aCaseItsOwnRulesRefuseLeavesTheInputItsOtherCases() {
        assertEquals(Optional.empty(), emptinessOf(DEAD_CASE),
                "every B is a row this behavior takes, so the input is not proved empty");
    }

    @Test
    void andSoDoesACaseRefusedOnlyOnceTheRelationIsCarried() {
        assertEquals(Optional.empty(), emptinessOf(DEAD_ONCE_THE_RELATION_IS_CARRIED),
                "every B is a row this behavior takes, so the input is not proved empty");
    }

    @Test
    void aSequenceInsideACaseIsRefusedNoFurtherThanTheCase() {
        assertEquals(Optional.empty(), emptinessOf(A_SEQUENCE_INSIDE_A_CASE),
                "every B is a row this behavior takes, whatever A's list would have to hold");
    }

    @Test
    void andACaseInsideASequenceLeavesTheSequenceItsOtherCase() {
        assertEquals(Optional.empty(), emptinessOf(A_CASE_INSIDE_A_SEQUENCE),
                "a list of Items that are all B is a row this behavior takes");
    }

    @Test
    void anEmptySequenceIsAValueWhateverItsElementWouldBe() {
        assertEquals(Optional.empty(), emptinessOf(MAY_BE_EMPTY),
                "an empty list is a row this behavior takes");
    }

    @Test
    void andOneThatCannotBeEmptyIsRefusedByWhatItWouldHold() {
        Optional<EmptyInput> why = emptinessOf(HOLDS_AT_LEAST_ONE);

        assertTrue(why.isPresent(), "the list holds an Item and there is no Item to hold");
        Emptiness proof = ((EmptyInput.ProvedByTheRules) why.orElseThrow()).why();
        Emptiness.AtAField at = assertInstanceOf(Emptiness.AtAField.class, proof,
                "the lack is at the container, which is the place a reader is sent to");
        assertEquals(new Emptiness.AtAField.Where.In("h.items"), at.where());
        assertInstanceOf(Emptiness.NonEmptyCollectionWithNoElement.class, at.under(),
                "and it says which of the two facts it took to refuse the input");
    }

    @Test
    void andTheRuleAboutTheLengthRefusesNothingOnItsOwn() {
        assertEquals(Optional.empty(), emptinessOf(AND_AN_ELEMENT_THAT_STANDS),
                "a list of one Item is a row this behavior takes");
    }

    @Test
    void aSumNothingIsKnownAboutDoesNotHideWhatTheSumBesideItRefuses() {
        for (String source : List.of(UNREAD_BESIDE_REFUSED, REFUSED_BESIDE_UNREAD)) {
            assertTrue(emptinessOf(source).isPresent(),
                    "no value of Q exists, so no row does, whatever was read of the tree");
        }
    }

    @Test
    void andWhichOfTheTwoIsDeclaredFirstIsNoPartOfTheAnswer() {
        assertEquals(emptinessOf(UNREAD_BESIDE_REFUSED), emptinessOf(REFUSED_BESIDE_UNREAD),
                "the same two structures, whichever order the fields were written in");
    }

    @Test
    void andASequenceThatCannotBeFilledIsNotHiddenEither() {
        assertTrue(emptinessOf(UNREAD_BESIDE_A_DEAD_ELEMENT).isPresent(),
                "the list holds an Item and there is no Item to hold");
    }

    @Test
    void whatTheValueAboveBoundsOnAnOrderMeetsWhatTheCaseBounds() {
        assertTrue(emptinessOf(ON_AN_ORDER).isPresent(),
                "no tag is both at most \"A\" and at least \"M\", so no case of Q has a value");
    }

    @Test
    void andWhichValuesItAdmitsMeetsWhatTheCaseAdmits() {
        assertTrue(emptinessOf(ON_THE_VALUES).isPresent(),
                "no tag is both \"A\" and not \"A\", so no case of Q has a value");
    }

    /** And with the rule above taken out, each of them leaves the input its values. */
    @Test
    void andWithoutTheRuleAboveNothingRefusesTheInput() {
        for (String source : List.of(ON_AN_ORDER_UNRULED, ON_THE_VALUES_UNRULED)) {
            assertEquals(Optional.empty(), emptinessOf(source),
                    "what one case says of the name refuses nothing on its own");
        }
    }

    private static Optional<EmptyInput> emptinessOf(String source) {
        InputDomain read = reading(source, "read");
        return read.quantities(rulesOf(source)).emptiness();
    }

    private static RuleReadingSource rulesOf(String source) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.answerEverything();
        return RuleReadings.of(compilation, compilation.modules().get(0));
    }

    private static InputDomain reading(String source, String behavior) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        return InputDomain.of(sigs.get(behavior),
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES));
    }
}
