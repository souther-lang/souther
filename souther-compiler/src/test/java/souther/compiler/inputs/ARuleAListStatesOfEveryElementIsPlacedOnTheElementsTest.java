package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.TestDay;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.ElementGuarantee;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.PartId;
import souther.compiler.check.RuleKey;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.RuleRef;
import souther.compiler.check.TypeCardinality;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

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

    /** Both statements of every element are one rule's, written as one conjunction. */
    private static final String TWO_STATEMENTS_IN_ONE_RULE = """
            module bounded

            data Ws = List<String> invariant
                List.all(s -> String.length(s) <= 10, value)
                && List.all(s -> String.length(s) <= 7, value)

            data Ok

            behavior f : (ws: Ws) -> Ok
            """;

    private static final String ELEMENTS_THAT_ARE_RECORDS = """
            module bounded

            data Entry = { size: Int, other: Int }

            data Entries = List<Entry> invariant List.all(e -> e.size <= 10, value)

            data Ok

            behavior f : (entries: Entries) -> Ok
            """;

    /** The element is handed on whole, which no field of it stands for. */
    private static final String ELEMENTS_ASKED_AS_A_WHOLE = """
            module bounded

            data Entry = { size: Int, other: Int }

            data Entries = List<Entry> invariant List.all(e -> e == e, value)

            data Ok

            behavior f : (entries: Entries) -> Ok
            """;

    private static final String ELEMENTS_WITH_NOTHING_STATED = """
            module bounded

            data Entry = { size: Int, other: Int }

            data Entries = List<Entry>

            data Ok

            behavior f : (entries: Entries) -> Ok
            """;

    private static final String ELEMENTS_THAT_ARE_ONE_OF_SEVERAL = """
            module bounded

            data A
            data B
            data Q = A | B

            data Qs = List<Q> invariant List.all(q -> q == A, value)

            data Ok

            behavior f : (qs: Qs) -> Ok
            """;

    private static final String ELEMENTS_THAT_ARE_NEWTYPES = """
            module bounded

            data N = Int invariant value >= -100

            data Ns = List<N> invariant List.all(n -> n == n, value)

            data Ok

            behavior f : (ns: Ns) -> Ok
            """;

    /** The rule is written on the record that holds the list, and the elements wear a declaration. */
    private static final String DECLARED_ELEMENTS_IN_A_RECORDS_FIELD = """
            module bounded

            data Entry = { size: Int, other: Int }

            data R = { entries: List<Entry> } invariant List.all(e -> e.size <= 10, entries)

            data Ok

            behavior f : (r: R) -> Ok
            """;

    /** Two statements, each about another field of the element. */
    private static final String EACH_STATEMENT_ABOUT_ANOTHER_FIELD = """
            module bounded

            data Entry = { size: Int, other: Int }

            data Entries = List<Entry> invariant
                List.all(e -> e.size <= 10, value) && List.all(e -> e.other <= 5, value)

            data Ok

            behavior f : (entries: Entries) -> Ok
            """;

    private static final String LISTS_OF_LISTS = """
            module bounded

            data Ws = List<List<String>> invariant
                List.all(l -> List.all(s -> String.length(s) <= 10, l), value)

            data Ok

            behavior f : (ws: Ws) -> Ok
            """;

    /** The statement is about the strings that pass a test, and not about every string. */
    private static final String ONLY_THE_ELEMENTS_THAT_PASS = """
            module bounded

            data Ws = List<String> invariant
                List.all(s -> String.length(s) <= 10, List.filter(s -> String.length(s) > 3, value))

            data Ok

            behavior f : (ws: Ws) -> Ok
            """;

    /** The element is a newtype, and the statement names it as it is or by what it wraps. */
    private static String newtypeElements(String statement) {
        return """
                module bounded

                data N = Int invariant value >= -100

                data Ns = List<N> invariant List.all(n -> %s, value)

                data Ok

                behavior f : (ns: Ns) -> Ok
                """.formatted(statement);
    }

    private static final String NEWTYPE_ELEMENTS_OVER_STRINGS = """
            module bounded

            data W = String invariant String.length(value) <= 20

            data Ws = List<W> invariant List.all(w -> String.length(w.value) <= 10, value)

            data Ok

            behavior f : (ws: Ws) -> Ok
            """;

    private static final String NEWTYPE_FIELDS_OF_ELEMENTS = """
            module bounded

            data N = Int invariant value >= -100

            data R = { n: N, k: Int }

            data Rs = List<R> invariant List.all(r -> r.n.value <= 10 && r.k <= 3, value)

            data Ok

            behavior f : (rs: Rs) -> Ok
            """;

    /** The elements are of the kind that holds them, so the rule is the elements' own as well. */
    private static final String ELEMENTS_OF_ITS_OWN_KIND = """
            module bounded

            data Issue = { size: Int, more: List<Issue> }
                invariant List.all(each -> each.size <= 10, more)

            data Ok

            behavior f : (i: Issue) -> Ok
            """;

    /** And the statement names a field of the value that holds the list, which is the same name. */
    private static final String ELEMENTS_OF_ITS_OWN_KIND_AGAINST_THE_HOLDER = """
            module bounded

            data Issue = { size: Int, more: List<Issue> }
                invariant List.all(each -> each.size <= size, more)

            data Ok

            behavior f : (i: Issue) -> Ok
            """;

    /** The statement names a field of the holder, which the element's reading holds no value of. */
    private static String statedAgainstTheHolder(String entry, String holder) {
        return """
                module bounded

                data Entry = { %s }

                data R = { limit: Int, entries: List<Entry> } invariant
                    %s List.all(e -> e.amount <= limit, entries)

                data Ok

                behavior f : (r: R) -> Ok
                """.formatted(entry, holder);
    }

    /** Two statements of every element made by one part, a helper the rule calls. */
    private static final String TWO_STATEMENTS_BY_ONE_PART = """
            module bounded

            let bounded (xs: List<Int>): Bool =
                List.all(x -> x >= 2, xs) && List.all(x -> x <= 7, xs)

            data Ns = List<Int> invariant bounded(value)

            data Ok

            behavior f : (ns: Ns) -> Ok
            """;

    /** The same two, as two parts of the rule. */
    private static final String TWO_STATEMENTS_BY_TWO_PARTS = """
            module bounded

            data Ns = List<Int> invariant
                List.all(x -> x >= 2, value) && List.all(x -> x <= 7, value)

            data Ok

            behavior f : (ns: Ns) -> Ok
            """;

    /** Both said of one element by one statement. */
    private static final String TWO_BOUNDS_IN_ONE_STATEMENT = """
            module bounded

            data Ns = List<Int> invariant List.all(x -> x >= 2 && x <= 7, value)

            data Ok

            behavior f : (ns: Ns) -> Ok
            """;

    private static RuleReadingContext readingOf(Compilation compilation) {
        RuleReadingSource rules = RuleReadings.of(compilation, compilation.modules().get(0));
        return RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
    }

    private static Position positionOf(String source, String path) {
        Compilation compilation = ACompiledModel.answered(source);
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingContext reading = readingOf(compilation);
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

    /**
     * A rule says what it says however its statements are joined: two of them in one conjunction
     * are two statements of every element, and both stop the strings.
     */
    @Test
    void twoStatementsOfEveryElementInOneRuleAreStatedAsTwoRulesAre() {
        Position together = positionOf(TWO_STATEMENTS_IN_ONE_RULE, "ws[*]");
        Position apart = positionOf(TWO_RULES_OVER_THE_ELEMENTS, "ws[*]");
        assertEquals(Endpoint.inclusive(Count.of(7)), longest(together));
        assertEquals(longest(apart), longest(together));
        assertEquals(apart.completeness().getClass(), together.completeness().getClass());
    }

    /**
     * The two statements keep the names they were written under, so that each is a part a reading
     * can be made without: leaving out one leaves what the other places.
     */
    @Test
    void eachOfTwoStatementsInOneRuleCanBeLeftOutOnItsOwn() {
        Compilation compilation = ACompiledModel.answered(TWO_STATEMENTS_IN_ONE_RULE);
        String module = compilation.modules().get(0);
        DeclaredSig sig =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value().get("f");
        RuleReadingContext reading = readingOf(compilation);
        PlacedRules container = PlacedRules.of(TermPath.of("ws"), sig.inputs().getFirst().type(),
                reading);
        List<ElementGuarantee> stated = container.guaranteedOfEveryElementAt(TermPath.of("ws"));
        assertEquals(2, stated.size());
        assertEquals(1, stated.stream().map(each -> each.part().rule()).distinct().count(),
                "both are parts of the one rule");
        FieldDomains element = FieldDomains.ofElement(null, Type.STRING, stated, reading);
        Set<PartId<RuleRef.Invariant>> both = stated.stream().map(ElementGuarantee::part)
                .collect(Collectors.toSet());
        assertEquals(both, placingTheLength(element));
        for (ElementGuarantee left : stated) {
            Set<PartId<RuleRef.Invariant>> other = new HashSet<>(both);
            other.remove(left.part());
            assertEquals(other, placingTheLength(element.leavingOut(Set.of(left.part()))));
        }
        assertEquals(Set.of(), placingTheLength(element.leavingOut(both)));
    }

    /**
     * What is said of a rule does not turn on the order its statements were written in: the parts
     * it holds a position down by, and the ones it does not, are the same whichever comes first.
     */
    @Test
    void whatIsSaidOfARuleDoesNotTurnOnTheOrderOfItsStatements() {
        String narrows = "List.all(s -> s /= \"a\", value)";
        String leaves = "List.all(s -> s == s, value)";
        assertEquals(List.of(true, false), whichStatementsAreSaidToHoldTheStringsDown(
                ws(narrows + " && " + leaves)));
        assertEquals(List.of(false, true), whichStatementsAreSaidToHoldTheStringsDown(
                ws(leaves + " && " + narrows)));
    }

    private static String ws(String invariant) {
        return "module bounded\ndata Ws = List<String> invariant " + invariant
                + "\ndata Ok\nbehavior f : (ws: Ws) -> Ok\n";
    }

    /**
     * For each statement the list makes of its elements, in the order it was written, whether the
     * elements' reading says it holds the strings to fewer values.
     */
    private static List<Boolean> whichStatementsAreSaidToHoldTheStringsDown(String source) {
        Compilation compilation = ACompiledModel.answered(source);
        String module = compilation.modules().get(0);
        DeclaredSig sig =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value().get("f");
        RuleReadingContext reading = readingOf(compilation);
        PlacedRules container = PlacedRules.of(TermPath.of("ws"), sig.inputs().getFirst().type(),
                reading);
        List<ElementGuarantee> stated = container.guaranteedOfEveryElementAt(TermPath.of("ws"));
        Set<PartId<RuleRef.Invariant>> holding =
                FieldDomains.ofElement(null, Type.STRING, stated, reading).noLines().stream()
                        .filter(each -> each.why()
                                instanceof BlockReason.RuleRestrictingToAdmittedValues)
                        .map(FieldDomains.NoLine::part).collect(Collectors.toSet());
        return stated.stream().map(each -> holding.contains(each.part())).toList();
    }

    /**
     * What a part of a rule states is stated of the elements by that part, however many things it
     * states: a helper that makes two statements is one part, and the reading is made without it as
     * a whole. The two spelled as two parts of the rule are two, each left out on its own.
     */
    @Test
    void severalStatementsOfOnePartAreThatPartsAndNotSeveralParts() {
        for (String model : new String[] {TWO_STATEMENTS_BY_ONE_PART, TWO_STATEMENTS_BY_TWO_PARTS,
                TWO_BOUNDS_IN_ONE_STATEMENT}) {
            Position at = positionOf(model, "ns[*]");
            assertEquals(Endpoint.inclusive(Count.of(2)), at.bounds().getFirst().admissible().min(),
                    model);
            assertEquals(Endpoint.inclusive(Count.of(7)), at.bounds().getFirst().admissible().max(),
                    model);
        }
        Compilation compilation = ACompiledModel.answered(TWO_STATEMENTS_BY_ONE_PART);
        String module = compilation.modules().get(0);
        DeclaredSig sig =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value().get("f");
        RuleReadingContext reading = readingOf(compilation);
        List<ElementGuarantee> stated = PlacedRules.of(TermPath.of("ns"),
                sig.inputs().getFirst().type(), reading)
                .guaranteedOfEveryElementAt(TermPath.of("ns"));
        assertEquals(2, stated.size(), "the helper states two things of each element");
        Set<PartId<RuleRef.Invariant>> parts =
                stated.stream().map(ElementGuarantee::part).collect(Collectors.toSet());
        assertEquals(1, parts.size(), "and it is one part of the rule");
        FieldDomains element = FieldDomains.ofElement(null, Type.INT, stated, reading);
        assertEquals(2, element.placedAt(RuleKey.THE_VALUE).stream()
                .map(FieldDomains.Placed::from).distinct().count(),
                "each end is the statement that put it there, and the two are not one");
        assertEquals(parts, element.placedAt(RuleKey.THE_VALUE).stream()
                .map(FieldDomains.Placed::part).collect(Collectors.toSet()),
                "both ends are that part's");
        assertEquals(List.of(), element.leavingOut(parts).placedAt(RuleKey.THE_VALUE),
                "and leaving it out leaves neither");
    }

    private static Set<PartId<RuleRef.Invariant>> placingTheLength(FieldDomains domains) {
        return domains.placedAt(RuleKey.THE_VALUE).stream().map(FieldDomains.Placed::part)
                .collect(Collectors.toSet());
    }

    /** An element that is a record is stopped at the fields the statement is about. */
    @Test
    void whatAListStatesOfEachRecordItHoldsStopsTheFieldItNames() {
        assertEquals(Endpoint.inclusive(Count.of(10)),
                positionOf(ELEMENTS_THAT_ARE_RECORDS, "entries[*].size").bounds().getFirst()
                        .admissible().max());
        assertNull(positionOf(ELEMENTS_THAT_ARE_RECORDS, "entries[*].other").bounds().getFirst()
                .admissible());
    }

    /**
     * What a list states of an element it cannot place in the element's fields is not dropped
     * unsaid: the position was read short of it, and a position with nothing stated of the
     * elements was not.
     */
    @Test
    void andWhatItCannotPlaceInTheFieldsLeavesThePositionShortOfIt() {
        assertInstanceOf(AdmissibleSet.Completeness.Complete.class,
                positionOf(ELEMENTS_WITH_NOTHING_STATED, "entries[*].size").completeness());
        assertInstanceOf(AdmissibleSet.Completeness.Wider.class,
                positionOf(ELEMENTS_ASKED_AS_A_WHOLE, "entries[*].size").completeness());
    }

    /**
     * What a statement names of the container that holds the list is no place of an element, and the
     * element is not stopped by it however the container's own rules leave that name: bound,
     * unbound, or a name the element's declaration has as well.
     */
    @Test
    void aStatementNamingAFieldOfTheHolderStopsNoElementAndSaysItIsUnread() {
        for (String model : new String[] {
                statedAgainstTheHolder("amount: Int", "limit == 3 &&"),
                statedAgainstTheHolder("amount: Int", ""),
                statedAgainstTheHolder("amount: Int, limit: Int", "limit == 3 &&")}) {
            Position amount = positionOf(model, "r.entries[*].amount");
            assertNull(amount.bounds().getFirst().admissible(), model);
            assertInstanceOf(AdmissibleSet.Completeness.Wider.class, amount.completeness(), model);
            // The statement never reached the element, rather than reached it and been read as
            // something the element's own places did not say.
            assertTrue(amount.unansweredQuestions().isEmpty(), model);
        }
        Position own = positionOf(statedAgainstTheHolder("amount: Int, limit: Int",
                "limit == 3 &&"), "r.entries[*].limit");
        assertNull(own.bounds().getFirst().admissible());
    }

    /** A choice between cases is not read the container's statement into, and says so. */
    @Test
    void anElementThatIsOneOfSeveralCasesIsSaidToBeUnreadWhereTheListStatesSomething() {
        assertInstanceOf(AdmissibleSet.Completeness.Wider.class,
                positionOf(ELEMENTS_THAT_ARE_ONE_OF_SEVERAL, "qs[*]").completeness());
    }

    @Test
    void asItDoesWhereTheRuleIsOnTheRecordHoldingAListOfRecords() {
        assertEquals(Endpoint.inclusive(Count.of(10)),
                positionOf(DECLARED_ELEMENTS_IN_A_RECORDS_FIELD, "r.entries[*].size").bounds()
                        .getFirst().admissible().max());
        assertNull(positionOf(DECLARED_ELEMENTS_IN_A_RECORDS_FIELD, "r.entries[*].other").bounds()
                .getFirst().admissible());
    }

    @Test
    void andEachOfTwoStatementsStopsTheFieldItIsAbout() {
        assertEquals(Endpoint.inclusive(Count.of(10)),
                positionOf(EACH_STATEMENT_ABOUT_ANOTHER_FIELD, "entries[*].size").bounds()
                        .getFirst().admissible().max());
        assertEquals(Endpoint.inclusive(Count.of(5)),
                positionOf(EACH_STATEMENT_ABOUT_ANOTHER_FIELD, "entries[*].other").bounds()
                        .getFirst().admissible().max());
    }

    @Test
    void andWhatAListOfListsStatesOfEachElementOfEachListStopsTheStringsInThem() {
        assertEquals(Endpoint.inclusive(Count.of(10)),
                longest(positionOf(LISTS_OF_LISTS, "ws[*][*]")));
    }

    /** What is stated of the strings that pass a test says nothing of the ones that do not. */
    @Test
    void whatIsStatedOfOnlyTheElementsThatPassATestStopsNoElement() {
        assertNull(longest(positionOf(ONLY_THE_ELEMENTS_THAT_PASS, "ws[*]")));
    }

    /**
     * A newtype is compared by what it wraps, so naming it as it is and naming what it wraps say
     * the same: the element holds its own rules and what the list states, either way written.
     */
    @Test
    void aNewtypeElementIsStoppedTheSameWhetherItIsNamedWholeOrByWhatItWraps() {
        Position whole = positionOf(newtypeElements("n <= 10"), "ns[*]");
        Position wrapped = positionOf(newtypeElements("n.value <= 10"), "ns[*]");
        for (Position each : List.of(whole, wrapped)) {
            assertEquals(Endpoint.inclusive(Count.of(-100)),
                    each.bounds().getFirst().admissible().min());
            assertEquals(Endpoint.inclusive(Count.of(10)),
                    each.bounds().getFirst().admissible().max());
        }
        assertEquals(whole.completeness().getClass(), wrapped.completeness().getClass());
        assertEquals(whole.unansweredQuestions().size(), wrapped.unansweredQuestions().size());
    }

    /**
     * A rule is answered for once, and an element of the kind that holds it is read under that very
     * rule. What the list states of the element is then said to be unread, and not read beside the
     * element's own copy of it.
     */
    @Test
    void whatAListOfItsOwnKindStatesOfItsElementsIsSaidToBeUnread() {
        for (String model : new String[] {ELEMENTS_OF_ITS_OWN_KIND,
                ELEMENTS_OF_ITS_OWN_KIND_AGAINST_THE_HOLDER}) {
            assertInstanceOf(AdmissibleSet.Completeness.Wider.class,
                    positionOf(model, "i.more[*]").completeness(), model);
        }
        // And nothing is placed where the statement names the holder's own field: read as the
        // element's, `each.size <= size` would be a statement of the element alone.
        Compilation compilation = ACompiledModel.answered(
                ELEMENTS_OF_ITS_OWN_KIND_AGAINST_THE_HOLDER);
        String module = compilation.modules().get(0);
        DeclaredSig sig =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value().get("f");
        RuleReadingContext reading = readingOf(compilation);
        for (Position each : InputDomain.of(sig, reading,
                TypeCardinality.Counts.workedOutIn(reading),
                souther.compiler.carrier.Membership.none()).positions()) {
            if (each.path().toString().equals("i.more[*].size")) {
                assertNull(each.bounds().getFirst().admissible());
                assertInstanceOf(AdmissibleSet.Completeness.Wider.class, each.completeness());
            }
        }
    }

    @Test
    void aNewtypeOverStringsIsStoppedByTheShorterOfItsOwnRuleAndTheListsStatementOfIt() {
        assertEquals(Endpoint.inclusive(Count.of(10)),
                longest(positionOf(NEWTYPE_ELEMENTS_OVER_STRINGS, "ws[*]")));
    }

    @Test
    void aNewtypeFieldOfARecordElementIsStoppedAsAFieldOfOneIs() {
        Position field = positionOf(NEWTYPE_FIELDS_OF_ELEMENTS, "rs[*].n");
        assertEquals(Endpoint.inclusive(Count.of(-100)),
                field.bounds().getFirst().admissible().min());
        assertEquals(Endpoint.inclusive(Count.of(10)),
                field.bounds().getFirst().admissible().max());
        assertEquals(Endpoint.inclusive(Count.of(3)),
                positionOf(NEWTYPE_FIELDS_OF_ELEMENTS, "rs[*].k").bounds().getFirst()
                        .admissible().max());
    }

    /** An element that is a newtype keeps its own rules beside what the list states of it. */
    @Test
    void anElementThatIsANewtypeKeepsItsOwnRulesBesideWhatTheListStatesOfIt() {
        Position at = positionOf(ELEMENTS_THAT_ARE_NEWTYPES, "ns[*]");
        assertEquals(Endpoint.inclusive(Count.of(-100)), at.bounds().getFirst().admissible().min());
    }
}
