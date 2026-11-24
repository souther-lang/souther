package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.ast.Hir;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.Carrier;
import souther.compiler.check.Prepared;
import souther.compiler.check.StatedContract;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which comparisons in an {@code ensures} draw a line, and which draw none (issue #823).
 *
 * <p>Three questions the clause reading has to answer, and each of them has a wrong answer that
 * reads as a line the model never drew. What the rule states outright is a line; what it states
 * under an {@code ||} is not. What it says about an input is a line; what it says about the answer
 * is not, because a row does not choose what a behavior answers. And a rule is read whether or not
 * anything implements the behavior, since a clause is written against the declaration.
 */
class WhatAClauseDrawsALineOnTest {

    /** The number the line below is on, which its orders are the orders of. */
    private static final souther.compiler.inputs.NumericTerm.ValueOf AT_ID =
            new souther.compiler.inputs.NumericTerm.ValueOf(
                    souther.compiler.inputs.TermPath.of("id"));

    /** The lines one behavior's clauses draw, through the readings a report is built from. */
    private static EnsuresThresholds.Clauses drawn(String source, String behavior) {
        return drawn(ACompiledModel.answered(source), behavior);
    }

    /** The same, over a model that is expected to be refused with {@code codes} and read anyway. */
    private static EnsuresThresholds.Clauses drawnDespite(
            List<String> codes, String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        ACompiledModel.refusedWith(codes, compilation);
        return drawn(compilation, behavior);
    }

    private static EnsuresThresholds.Clauses drawn(Compilation compilation, String behavior) {
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Map<String, StatedContract> stated =
                compilation.db().ask(new Bodies.StatedContracts(module)).value();
        InputDomain inputs =
                compilation.db().ask(new Adequacy.Inputs(module)).value().get(behavior);
        assertTrue(prepared.behaviors().stream()
                        .anyMatch(b -> b instanceof Hir.SpecBehavior && b.name().equals(behavior)),
                "the behavior under test is declared");
        return ThresholdFixtures.clausesOf(stated == null ? null : stated.get(behavior), inputs, rules);
    }

    private static List<String> valuesOf(EnsuresThresholds.Clauses clauses) {
        return clauses.thresholds().stream()
                .map(each -> each.path() + " = " + each.value().spelled()).toList();
    }

    /**
     * A comparison a clause states outright draws a line.
     *
     * <p>On a behavior nothing implements, which is the case a clause reaches and a {@code guard}
     * cannot: an injected behavior has no body, so what its declaration states is the whole of what
     * a report can hold an implementation to.
     */
    @Test
    void aComparisonARuleStatesOutrightDrawsALine() {
        EnsuresThresholds.Clauses clauses = drawn("""
                module g

                data TodoId = Int
                data Todo = { id: TodoId }
                data NotFound = { asked: TodoId }

                behavior findTodo : (id: TodoId) -> Todo | NotFound
                    ensures asked = NotFound -> id.value > 0
                """, "findTodo");

        assertEquals(1, clauses.thresholds().size(), valuesOf(clauses).toString());
        Threshold line = clauses.thresholds().get(0);
        assertEquals("id", line.path().toString());
        assertInstanceOf(LineOrigin.EnsuresOrigin.class, line.origin());
        assertEquals(new souther.compiler.check.ComparisonClaim.Cut(
                        souther.compiler.numeric.Towards.BELOW, false),
                ((LineOrigin.EnsuresOrigin) line.origin()).facts().claim(),
                "`> 0` puts the zero on the low side and is not met there, so the row beside it is"
                        + " the one above");
    }

    /** And the clause is named the way a reader will look for it: by the name its author gave it. */
    @Test
    void theLineIsNamedAfterTheClause() {
        EnsuresThresholds.Clauses clauses = drawn("""
                module g

                data TodoId = Int
                data Todo = { id: TodoId }
                data NotFound = { asked: TodoId }

                behavior findTodo : (id: TodoId) -> Todo | NotFound
                    ensures asked = NotFound -> id.value > 0
                """, "findTodo");

        assertEquals("ensures findTodo (asked)", clauses.thresholds().get(0).origin().saidWithoutAPlace());
    }

    /** Where the author named no clause, the case the arm is about is what is left to say. */
    @Test
    void anUnnamedClauseIsNamedByTheCaseTheArmIsAbout() {
        EnsuresThresholds.Clauses clauses = drawn("""
                module g

                data TodoId = Int
                data Todo = { id: TodoId }
                data NotFound = { asked: TodoId }

                behavior findTodo : (id: TodoId) -> Todo | NotFound
                    ensures NotFound -> id.value > 0
                """, "findTodo");

        assertEquals("ensures findTodo (NotFound)", clauses.thresholds().get(0).origin().saidWithoutAPlace());
    }

    /**
     * Both sides of an {@code &&} are stated, so both draw a line.
     *
     * <p>Which is what a conjunction means: the rule holds only where both hold, so a row that
     * reaches the rule at all has met both.
     */
    @Test
    void bothSidesOfAConjunctionDrawALine() {
        EnsuresThresholds.Clauses clauses = drawn("""
                module g

                data TodoId = Int
                data Todo = { id: TodoId }
                data NotFound = { asked: TodoId }

                behavior findTodo : (id: TodoId) -> Todo | NotFound
                    ensures asked = NotFound -> id.value > 0 && id.value < 100
                """, "findTodo");

        assertEquals(List.of("id = 0", "id = 100"), valuesOf(clauses));
    }

    /**
     * A disjunct draws none.
     *
     * <p>{@code a || b} says nothing about where {@code a} changes: the rule holds wherever
     * {@code b} does, whatever {@code a} comes to. A line read off one side would be a distinction
     * put into the partition that the model never drew, and the rows would be asked to cover it.
     */
    @Test
    void aDisjunctDrawsNoLine() {
        String model = """
                module g

                data TodoId = Int
                data Todo = { id: TodoId }
                data NotFound = { asked: TodoId, urgent: Bool }

                behavior findTodo : (id: TodoId, urgent: Bool) -> Todo | NotFound
                    ensures asked = NotFound -> id.value > 0 %s urgent
                """;

        // The same rule with the operator changed, so that "no line" is the disjunction's answer
        // and not a rule this reading never got to at all.
        assertEquals(List.of("id = 0"), valuesOf(drawn(model.formatted("&&"), "findTodo")));
        assertEquals(List.of(), valuesOf(drawn(model.formatted("||"), "findTodo")),
                "neither side of a disjunction is stated on its own");
    }

    /**
     * A comparison on the answer draws none either.
     *
     * <p>The line is real — the relation does change there — and it is not one a row can be written
     * at: what a row chooses is what the behavior is applied to, and what it answers is the
     * behavior's. An obligation at such a value would be work nobody can do.
     */
    @Test
    void aComparisonOnTheAnswerDrawsNoLine() {
        String model = """
                module g

                data Count = Int
                data Total = Int

                behavior tally : (n: Count) -> Total
                    ensures %s.value > 0
                """;

        // The same clause over the input, so that "no line" is what reading the answer comes to
        // rather than what this reading does with every clause of this shape. Each clause names
        // only one side, so each model is refused for it and is read all the same.
        assertEquals(List.of("n = 0"),
                valuesOf(drawnDespite(List.of("E1616"), model.formatted("n"), "tally")));
        assertEquals(List.of(),
                valuesOf(drawnDespite(List.of("E1617"), model.formatted("value"), "tally")),
                "a row cannot be written at a value the behavior answers with");
    }

    /**
     * And a rule relating the answer to an input is not a rule this could not read.
     *
     * <p>The other half of the same decision, and the opposite mistake. {@code value.sku ==
     * item.sku} was read and understood, and it draws no line a row can be written at — reported as
     * one this compiler did not read, it sends an author after a limit that is not there.
     *
     * <p><b>And the reason it raises nothing is the answer.</b> An equality between two things that
     * both move with the row raises nothing either, so this clause came back raising nothing while
     * classified as a rule about a pair of inputs — right for the wrong reason, and the reason is
     * what a reader is given. What the same shape written {@code <=} did is issue #1013 and the
     * test below.
     */
    @Test
    void aRuleRelatingTheAnswerToAnInputIsNotNamedAsUnread() {
        EnsuresThresholds.Clauses clauses = drawn("""
                module g

                data Sku = String
                data Item = { sku: Sku }
                data Found = { sku: Sku }

                behavior look : (item: Item) -> Found
                    ensures value.sku == item.sku
                """, "look");

        assertEquals(List.of(), valuesOf(clauses));
        assertEquals(List.of(), clauses.noLine().reported(),
                "this read the rule; what it draws no line at is a decision and not a limit");
        assertEquals(List.of(), clauses.noLine().unclassified(),
                "and nothing about it went unclassified");
        assertEquals(List.of(), clauses.between(),
                "and it is not a line between two inputs either: what it relates is the answer,"
                        + " which is what the classification says of it");
    }

    /**
     * The same shape written as an order raises nothing either (issue #1013).
     *
     * <p>Which it did not. An equality between two moving things raises nothing whatever they are,
     * so the clause above was silent while misclassified; an order between two of them is a line
     * rows are owed at, and where one of the two is the answer that line is at a place no reading
     * of the clause can reach. So the report named a rule nothing accounted for, about a behavior
     * whose every rule was read.
     *
     * <p>Nothing is left standing either. The rule was read and it names {@code query.limit} — a
     * row does choose that — and what follows is that it asks nothing of a measure over the input's
     * values. Which of the ways of asking nothing this is, is the classification's own answer and
     * is fixed where the classification is.
     */
    @Test
    void anOrderBetweenTheAnswerAndAnInputRaisesNothing() {
        EnsuresThresholds.Clauses clauses = drawn("""
                module g

                data Limit = Int
                data GlobalQuery = { limit: Limit }
                data Page = { articles: List<String> }

                behavior readArticles : (query: GlobalQuery) -> Page
                    ensures List.length(value.articles) <= query.limit.value
                """, "readArticles");

        assertEquals(List.of(), valuesOf(clauses), "the line is on the answer, and a row has none");
        assertEquals(List.of(), clauses.between(), "and it is not a line between two inputs");
        assertEquals(List.of(), clauses.noLine().reported(),
                "this read the rule; that it draws no line is a decision and not a limit");
        assertEquals(List.of(), clauses.noLine().unclassified(),
                "and nothing about it went unclassified");

    }

    /**
     * An equality singles the value out rather than ordering the values either side.
     *
     * <p>The same answer a {@code guard} writing one gets. What an equality distinguishes is the
     * value from every other value, so there is no neighbour to ask for.
     */
    @Test
    void anEqualitySinglesTheValueOut() {
        EnsuresThresholds.Clauses clauses = drawn("""
                module g

                data TodoId = Int
                data Todo = { id: TodoId }
                data NotFound = { asked: TodoId }

                behavior findTodo : (id: TodoId) -> Todo | NotFound
                    ensures asked = NotFound -> id.value == 0
                """, "findTodo");

        assertEquals(List.of(), valuesOf(clauses));
        assertEquals(1, clauses.singled().size(), clauses.singled().toString());
        Border singled = Border.at(BoundaryTarget.at(
                        new BorderQuantity.OfACoordinate("findTodo", AT_ID,
                                souther.compiler.inputs.TermOrdersFixtures
                                        .itself(AT_ID, new Carrier.Whole())),
                        new Level.OnACarrier(new Carrier.Whole(),
                                clauses.singled().get(0).value())),
                clauses.singled().get(0).origin(), null);
        assertEquals(List.of("ON = 0", "OFF below the line = -1", "OFF above the line = 1"),
                singled.answers().keySet().stream().filter(DomainPoint::againstTheLine)
                        .map(point -> singled.named(point) + " = " + singled.against(point))
                        .toList(),
                "the value a clause singles out, and the nearest value on each side of it, which"
                        + " are the two the clause keeps out");
    }

    /**
     * A measure of a location draws a line where the location's own value does.
     *
     * <p>What a line can be drawn on is one list (ADR-0090, spec §boundary-coordinates): the content
     * of a location, or {@code List.length}, {@code String.length}, {@code Set.size},
     * {@code Map.size} taken of one. A rule is read the same way wherever it is written, so a clause
     * over a length draws the line a {@code guard} over the same length draws.
     *
     * <p>It did not. A declaration's rules are read in the representation that keeps the operations
     * the language defines the meaning of standing, so the call arrives as a
     * {@code Core.PreservedCall} and not as the {@code Core.Call} a body's condition holds — and the
     * reader recognised one shape. Semantically the same call, in two trees; the position came back
     * as one this compiler could not read a rule about.
     */
    @Test
    void aMeasureOfALocationDrawsALine() {
        for (String measure : List.of("String.length(name.value)", "List.length(tags)")) {
            EnsuresThresholds.Clauses clauses = drawn("""
                    module g

                    data Name = String
                    data Found = { name: Name }
                    data NotFound = { asked: Name }

                    behavior find : (name: Name, tags: List<String>) -> Found | NotFound
                        ensures NotFound -> %s > 3
                    """.formatted(measure), "find");

            assertEquals(1, clauses.thresholds().size(),
                    () -> measure + " draws a line: " + valuesOf(clauses));
            assertEquals(List.of(), clauses.noLine().reported(),
                    () -> measure + " was read, so nothing says otherwise: "
                            + clauses.noLine().reported());
            assertEquals(List.of(), clauses.noLine().unclassified(),
                    () -> measure + " was read, so nothing about it is unclassified: "
                            + clauses.noLine().unclassified());
            assertTrue(clauses.thresholds().get(0).term() instanceof NumericTerm.TakenOf,
                    () -> measure + " is a line on the measure: "
                            + clauses.thresholds().get(0).term());
        }
    }

    /**
     * A rule stated through a helper draws the lines the helper's own comparisons draw.
     *
     * <p>A call is expanded where the rules are read, so the conjunct arrives as the helper's body
     * under a binding of the call's argument. A walk that stopped at anything that is not a
     * comparison found the rule stating nothing — and the position then fell out of every answer and
     * was reported as one the model draws no line through, which the clause two tokens away
     * contradicts. A {@code let} is not a choice: what the expression comes to is its body.
     */
    @Test
    void aRuleStatedThroughAHelperDrawsItsLines() {
        EnsuresThresholds.Clauses clauses = drawn("""
                module g

                data N = Int
                data Amount = { n: N }
                data Ok = { n: Int }
                data Refused = { why: String }

                let big (a: Amount) : Bool = a.n.value > 100

                behavior charge : (a: Amount) -> Ok | Refused
                    ensures small = Refused -> big(a)
                """, "charge");

        assertEquals(List.of("a.n = 100"), valuesOf(clauses));
    }

    /** A behavior whose clause says what it says through {@code clause}, over an optional name. */
    private static EnsuresThresholds.Clauses findingByName(String helper, String clause) {
        return drawn("""
                module g

                data Account = { name: String, domain: String?, ok: Bool }
                data AccountNotFound

                %s

                behavior find : (name: String) -> Account | AccountNotFound
                    ensures %s
                """.formatted(helper, clause), "find");
    }

    /** What the reading says of a clause, for two spellings to be held to one another. */
    private static List<String> saidOf(EnsuresThresholds.Clauses clauses) {
        return List.of(valuesOf(clauses).toString(),
                clauses.noLine().reported().toString(),
                clauses.noLine().unclassified().toString(),
                clauses.between().toString());
    }

    /**
     * A rule about the answer reads the same whether it is written out or through a helper.
     *
     * <p>The helper's parameter is another name for the answer, and a {@code match} whose other
     * arm is a written {@code false} says that the arm is the case and what its body says.
     */
    @Test
    void aRuleAboutTheAnswerReadsTheSameThroughAHelper() {
        List<String> written = saidOf(findingByName("", "Account -> value.name == name"));

        assertEquals(written, saidOf(findingByName(
                "let sameName (name: String, a: Account): Bool = a.name == name",
                "Account -> sameName(name, value)")),
                "a helper with no branch");
        EnsuresThresholds.Clauses byMatch = findingByName("""
                let sameDomain (name: String, a: Account): Bool =
                    match a.domain with
                        | Some own -> own == name
                        | None -> false
                """, "Account -> sameDomain(name, value)");
        assertEquals(List.of(), byMatch.noLine().reported(), "a match whose other arm is false");
        assertEquals(List.of(), byMatch.noLine().unclassified());
    }

    /** A behavior over two inputs, whose clause is stated through {@code helper}. */
    private static EnsuresThresholds.Clauses statedThrough(String helper, String clause) {
        return drawn("""
                module g

                data Active
                data Inactive
                data Status = Active | Inactive
                data Account = { name: String, ok: Bool }
                data AccountNotFound

                %s

                behavior find : (name: String, limit: Int, status: Status) -> Account | AccountNotFound
                    ensures %s
                """.formatted(helper, clause), "find");
    }

    /**
     * A statement an arm of a {@code match} selects on is still a statement about what it selects
     * on, and a branch that is not a written {@code false} states neither side.
     */
    @Test
    void aBranchIsOnlyReadAsAConjunctionWhereTheOtherWayIsFalse() {
        // The match is true only where the status is Active, and that is about an input.
        EnsuresThresholds.Clauses onTheInput = statedThrough("""
                let isActive (s: Status, a: Account): Bool =
                    match s with
                        | Active -> a.ok
                        | Inactive -> false
                """, "Account -> isActive(status, value)");
        assertEquals(List.of("status"),
                onTheInput.noLine().unclassified().stream()
                        .map(each -> each.at().toString()).toList(),
                "the selection stays a statement about the input it selects on");

        // An else that is anything but false is a choice, and a choice states neither side.
        EnsuresThresholds.Clauses choice = statedThrough("""
                let either (limit: Int, a: Account): Bool =
                    if a.ok then limit > 0 else limit < 5
                """, "Account -> either(limit, value)");
        assertEquals(List.of(), valuesOf(choice));

        // Two arms that are not false: neither body is required by itself.
        EnsuresThresholds.Clauses twoBodies = statedThrough("""
                let both (limit: Int, s: Status): Bool =
                    match s with
                        | Active -> limit > 0
                        | Inactive -> limit < 0
                """, "Account -> both(limit, status)");
        assertEquals(List.of(), valuesOf(twoBodies));
    }

    /**
     * What a branch states about an input is still a line where the other thing it states is about
     * the answer.
     */
    @Test
    void anInputComparisonBesideARuleAboutTheAnswerStillDrawsItsLine() {
        EnsuresThresholds.Clauses clauses = statedThrough("""
                let sameAndPositive (name: String, limit: Int, a: Account): Bool =
                    if a.name == name then limit > 0 else false
                """, "Account -> sameAndPositive(name, limit, value)");
        // And with the branch written the other way round, which says the condition denied.
        EnsuresThresholds.Clauses denied = statedThrough("""
                let otherAndPositive (name: String, limit: Int, a: Account): Bool =
                    if a.name == name then false else limit > 0
                """, "Account -> otherAndPositive(name, limit, value)");
        assertEquals(List.of("limit = 0"), valuesOf(denied));

        assertEquals(List.of("limit = 0"), valuesOf(clauses));
        assertEquals(List.of(), clauses.noLine().reported());
    }

    /**
     * A value made of the answer is the answer's, whichever way it was got to.
     *
     * <p>Two ways a name comes to stand for something made of the answer, each of which must read
     * as the rule written out reads: a name a {@code let} gave to a field of it, and the case an
     * arm of a {@code match} selected of it. A field handed to a helper as an argument is the first
     * of these, since the argument is bound to the parameter by a {@code let}.
     */
    @Test
    void whatIsMadeOfTheAnswerIsTheAnswerWhicheverWayItIsGotTo() {
        String model = """
                module g

                data Active = { label: String }
                data Inactive
                data Status = Active | Inactive
                data Account = { name: String, status: Status }
                data AccountNotFound

                %s

                behavior find : (name: String) -> Account | AccountNotFound
                    ensures Account -> h(name, value)
                """;
        EnsuresThresholds.Clauses named = drawn(model.formatted("""
                let h (name: String, a: Account): Bool = {
                    let own = a.name
                    own == name
                }
                """), "find");
        EnsuresThresholds.Clauses selected = drawn(model.formatted("""
                let h (name: String, a: Account): Bool =
                    match a.status with
                        | Active as s -> s.label == name
                        | Inactive -> false
                """), "find");

        assertEquals(List.of(), unreadOf(named), "a name for a field");
        assertEquals(List.of(), unreadOf(selected), "a case selected");
    }

    /** What a reading left unread of the rules it was handed. */
    private static List<Object> unreadOf(EnsuresThresholds.Clauses clauses) {
        List<Object> unread = new ArrayList<>(clauses.noLine().reported());
        unread.addAll(clauses.noLine().unclassified());
        return unread;
    }

    /**
     * And the same spellings over an input are about the input: what makes a value the answer's is
     * what it is made of, so a name given to a field of an input, or the case selected of one, is
     * not mistaken for the answer.
     */
    @Test
    void whatIsMadeOfAnInputIsNotTheAnswer() {
        String model = """
                module g

                data Active = { label: String }
                data Inactive
                data Status = Active | Inactive
                data Account = { name: String, status: Status }
                data AccountNotFound

                %s

                behavior find : (name: String, other: Account) -> Account | AccountNotFound
                    ensures Account -> %s
                """;
        assertEquals(saidOf(drawn(model.formatted("", "other.name == name"), "find")),
                saidOf(drawn(model.formatted("""
                        let h (name: String, a: Account): Bool = {
                            let own = a.name
                            own == name
                        }
                        """, "h(name, other)"), "find")),
                "a name for a field");
        EnsuresThresholds.Clauses selected = drawn(model.formatted("""
                let h (name: String, a: Account): Bool =
                    match a.status with
                        | Active as s -> s.label == name
                        | Inactive -> false
                """, "h(name, other)"), "find");
        assertEquals(List.of("other.status"),
                selected.noLine().unclassified().stream()
                        .map(each -> each.at().toString()).toList(),
                "the selection stays a statement about the input it selects on");
    }

    /**
     * And a rule stated in a form this does not read names the position it is about.
     *
     * <p>The other half. Where the walk stops on something it has no rule for, the position has to
     * be named as one a rule was written about that this could not read — anything else reports the
     * model as drawing no line where it draws one.
     */
    @Test
    void aRuleInAFormThisDoesNotReadNamesItsPosition() {
        EnsuresThresholds.Clauses clauses = drawn("""
                module g

                data N = Int
                data Amount = { n: N }
                data Ok = { n: Int }
                data Refused = { why: String }

                behavior charge : (a: Amount) -> Ok | Refused
                    ensures small = Refused -> Bool.not(a.n.value > 100)
                """, "charge");

        assertEquals(List.of(), valuesOf(clauses));
        assertEquals(List.of("a.n"),
                clauses.noLine().unclassified().stream()
                        .map(each -> each.at().toString()).toList());
    }

    /**
     * A rule comparing one input against another draws a line between the two.
     *
     * <p>On neither position, so it divides neither and has no axis to come off — and it is still a
     * line, because the row where the two hold one count is what tells a rule written {@code <} from
     * one written {@code <=}. The position is named as one no line was read at as well: what the
     * partition could not read here it still could not read, and a boundary answering does not
     * answer for it.
     */
    @Test
    void aRuleComparingTwoInputsDrawsALineBetweenThem() {
        EnsuresThresholds.Clauses clauses = drawn("""
                module g

                data Minute = Int
                data Ok = { n: Int }
                data Refused = { why: String }

                behavior book : (from: Minute, to: Minute) -> Ok | Refused
                    ensures ordered = Ok -> from.value < to.value
                """, "book");

        assertEquals(List.of(), valuesOf(clauses), "the line is on neither position");
        assertEquals(1, clauses.between().size(), clauses.between().toString());
        // Turned into borders here, because a clause's lines are collected and arranged with a
        // body's before any of them is a border: what a border owes away from its line is a run of
        // what every rule about that quantity leaves.
        Border line = Border.allOf(clauses.between()).get(0);
        assertEquals("book/from = to",
                line.cut().named() + " = " + line.cut().right());
        assertEquals("from = to", line.label());
        assertInstanceOf(LineOrigin.EnsuresOrigin.class, line.origin());
        // The line divides neither position and still has two sides: a row where `from` is under
        // `to` is inside it and one where `from` is over `to` is outside, which is as much a
        // coverage item as the row on the line.
        // `<` is open at the line, so the pair one step under it is the ON point and the side
        // away from the border starts under that.
        assertEquals("= to - 1", line.demand(PointRole.ON).criterion().asked(line.cut().of()));
        // The two away from the line are runs of the distance rather than sides of it, so what
        // they ask for is written whole: how far apart the pair stands at each end of the run.
        assertEquals("in from < to - 1",
                line.demand(PointRole.IN).criterion().asked(line.cut().of()));
        assertEquals("in to < from", line.demand(PointRole.OUT).criterion().asked(line.cut().of()));
        assertEquals(List.of("from", "to"),
                clauses.noLine().reported().stream().map(each -> each.at().toString()).toList());
    }

    /**
     * {@code <} and {@code <=} between the same two positions are two lines and not one.
     *
     * <p>What the row on the line shows is which of them was written, and there is no class either
     * side of it to read that off instead — so the answer at the line is what tells the two rules
     * apart, and an origin that dropped it would merge them into one obligation.
     */
    @Test
    void twoRulesBetweenOnePairAreToldApartByWhatHoldsOnTheLine() {
        EnsuresThresholds.Clauses clauses = drawn("""
                module g

                data Minute = Int
                data Ok = { n: Int }
                data Refused = { why: String }

                behavior book : (from: Minute, to: Minute) -> Ok | Refused
                    ensures strictly = Ok -> from.value < to.value
                    ensures loosely = Ok -> from.value <= to.value
                """, "book");

        assertEquals(2, clauses.between().size(), clauses.between().toString());
        assertEquals(2, Border.allOf(clauses.between()).stream()
                        .map(Border::origin).distinct().count(),
                "one line, two rules, and a row on it shows which of them was written");
    }

    /**
     * A comparison this could not read names the position it is about.
     *
     * <p>Which is not the same as drawing nothing. A position left out of both answers is reported
     * as one the model draws no line through — a sentence about the model — and the model says
     * otherwise in the clause two tokens away. The two send a reader to different places: one to a
     * distinction their own model does not make, the other to a limit of this compiler.
     */
    @Test
    void aComparisonThisCannotReadNamesItsPosition() {
        EnsuresThresholds.Clauses clauses = drawn("""
                module g

                data TodoId = Int
                data Todo = { id: TodoId }
                data NotFound = { asked: TodoId }

                behavior findTodo : (id: TodoId) -> Todo | NotFound
                    ensures asked = NotFound -> Int.multiply(id.value, id.value) > 10
                """, "findTodo");

        assertEquals(List.of(), valuesOf(clauses), "nothing here reads a line out of that form");
        assertEquals(List.of("id"),
                clauses.noLine().unclassified().stream()
                        .map(each -> each.at().toString()).toList(),
                "and the place it was filed at is named rather than passed over");
    }

    /** A behavior stating nothing draws nothing, and asking is not an error. */
    @Test
    void aBehaviorThatStatesNothingDrawsNothing() {
        assertEquals(EnsuresThresholds.Clauses.NONE, drawn("""
                module g

                data TodoId = Int
                data Todo = { id: TodoId }

                behavior findTodo : (id: TodoId) -> Todo
                """, "findTodo"));
    }
}
