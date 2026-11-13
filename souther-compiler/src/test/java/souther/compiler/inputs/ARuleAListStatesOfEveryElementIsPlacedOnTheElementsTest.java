package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.TestDay;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A rule a list states of every element it holds is placed where the elements stand.
 *
 * <p>The discharge reads {@code List.all} as its predicate held of each element, and the position of
 * an element is read from what it is: so a rule written over the elements of a list was read by the
 * one and left unread by the other.
 */
class ARuleAListStatesOfEveryElementIsPlacedOnTheElementsTest {

    private static final String A_NEWTYPE_OVER_A_LIST = """
            module bounded

            data Ws = List<String> invariant
                List.length(value) <= 3 && List.all(s -> String.length(s) <= 10, value)

            data Ok

            behavior f : (ws: Ws) -> Ok
            """;

    private static final String NAMED_STRINGS = """
            module bounded

            data Ws = List<String> invariant
                List.length(value) <= 3 && List.all(s -> s == "a" || s == "bb", value)

            data Ok

            behavior f : (ws: Ws) -> Ok
            """;

    private static final String A_FIELD_OF_A_RECORD = """
            module bounded

            data R = { ws: List<String> } invariant List.all(s -> String.length(s) <= 10, ws)

            data Ok

            behavior f : (r: R) -> Ok
            """;

    private static final String TWO_RULES_OVER_THE_ELEMENTS = """
            module bounded

            data Ws = List<String>
                invariant short = List.all(s -> String.length(s) <= 10, value)
                invariant shorter = List.all(s -> String.length(s) <= 7, value)

            data Ok

            behavior f : (ws: Ws) -> Ok
            """;

    private static final String SOME_ELEMENT = """
            module bounded

            data Ws = List<String> invariant List.any(s -> String.length(s) <= 10, value)

            data Ok

            behavior f : (ws: Ws) -> Ok
            """;

    private static final String EVERY_ELEMENT_OR_SOMETHING_ELSE = """
            module bounded

            data Ws = List<String> invariant
                List.all(s -> String.length(s) <= 10, value) || List.length(value) <= 3

            data Ok

            behavior f : (ws: Ws) -> Ok
            """;

    private static final String A_BOUND_ON_THE_OUTSIDE = """
            module bounded

            data R = { limit: Int, ws: List<String> }
                invariant List.all(s -> String.length(s) <= limit, ws)

            data Ok

            behavior f : (r: R) -> Ok
            """;

    private static Position positionOf(String source, String path) {
        Compilation compilation = ACompiledModel.answered(source);
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        return InputDomain.of(sigs.get("f"), reading,
                TypeCardinality.Counts.workedOutIn(reading),
                souther.compiler.carrier.Membership.none()).positions().stream()
                .filter(p -> p.path().toString().equals(path))
                .findFirst().orElseThrow();
    }

    /** Where the length of the string at the position stops, or null where nothing stops it. */
    private static Endpoint longest(Position at) {
        return at.bounds().stream()
                .filter(each -> each.term().toString().startsWith("String.length("))
                .findFirst().orElseThrow().admissible().max();
    }

    @Test
    void whatAListOfStringsStatesOfEachStringStopsTheLengthOfTheStringsItHolds() {
        assertEquals(Endpoint.inclusive(Count.of(10)),
                longest(positionOf(A_NEWTYPE_OVER_A_LIST, "ws[*]")));
    }

    @Test
    void asItDoesWhereTheRuleIsWrittenOnAFieldOfARecord() {
        assertEquals(Endpoint.inclusive(Count.of(10)),
                longest(positionOf(A_FIELD_OF_A_RECORD, "r.ws[*]")));
    }

    @Test
    void andWhereTwoRulesStateItTheShorterOneStops() {
        assertEquals(Endpoint.inclusive(Count.of(7)),
                longest(positionOf(TWO_RULES_OVER_THE_ELEMENTS, "ws[*]")));
    }

    @Test
    void aRuleThatSomeElementSatisfiesSaysNothingOfEach() {
        assertNull(longest(positionOf(SOME_ELEMENT, "ws[*]")));
    }

    @Test
    void norDoesOneThatHoldsOnlyWhereSomethingElseDoesNot() {
        assertNull(longest(positionOf(EVERY_ELEMENT_OR_SOMETHING_ELSE, "ws[*]")));
    }

    @Test
    void aSetOfStringsStatedOfEachIsWhatTheElementAdmits() {
        AdmissibleSet admitted = positionOf(NAMED_STRINGS, "ws[*]").admitted();
        assertEquals(new ValueSet.Finite(Set.of(new Value.Text("a"), new Value.Text("bb"))),
                admitted.approximation());
        assertInstanceOf(AdmissibleSet.Completeness.Complete.class, admitted.completeness());
    }

    /**
     * The rule is the same whether it is written on the record that holds the list or on the type
     * the list is the value of, and the elements of the list a field holds are placed alike.
     */
    @Test
    void whereverTheRuleIsWrittenTheNumbersTheListHoldsAreStopped() {
        String onTheRecord = """
                module bounded
                data R = { x: List<Int>, y: List<Int> } invariant List.all(e -> e >= 0, x)
                data Ok
                behavior f : (r: R) -> Ok
                """;
        String onTheType = """
                module bounded
                data X = List<Int> invariant List.all(e -> e >= 0, value)
                data R = { x: X, y: List<Int> }
                data Ok
                behavior f : (r: R) -> Ok
                """;
        for (String model : new String[] {onTheRecord, onTheType}) {
            assertEquals(Endpoint.inclusive(Count.of(0)),
                    positionOf(model, "r.x[*]").bounds().getFirst().admissible().min(), model);
            assertNull(positionOf(model, "r.y[*]").bounds().getFirst().admissible(), model);
        }
    }

    /** The rule is written above a sum, and the list is one every case of it shares. */
    @Test
    void aRuleAboveASumReachesTheElementsOfAListTheCasesShare() {
        String model = """
                module bounded

                data Paging = { names: List<String> }
                data A = { ...Paging, x: Int }
                data B = { ...Paging, y: Int }
                data Q = A | B

                data Holder = { q: Q }
                    invariant fits = List.all(s -> String.length(s) <= 10, q.names)

                data Ok

                behavior f : (h: Holder) -> Ok
                """;
        for (String each : new String[] {"A", "B"}) {
            assertEquals(Endpoint.inclusive(Count.of(10)),
                    longest(positionOf(model, "h.q@" + each + ".names[*]")), each);
        }
    }

    @Test
    void aStringIsNotStoppedAtANumberAnotherPlaceOfTheRecordHolds() {
        assertNull(longest(positionOf(A_BOUND_ON_THE_OUTSIDE, "r.ws[*]")));
    }

    /**
     * What a rule relates to a place outside the element is not read as what the element holds, and
     * the position says it is short of the rule.
     */
    @Test
    void andSaysItWentUnreadWhereTheRuleNamesThatNumber() {
        assertInstanceOf(AdmissibleSet.Completeness.Wider.class,
                positionOf(A_BOUND_ON_THE_OUTSIDE, "r.ws[*]").completeness());
    }
}
