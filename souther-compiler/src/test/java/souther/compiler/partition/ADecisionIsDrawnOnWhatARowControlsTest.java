package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionArgument;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.types.ValueName;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a body decides on is a position of its input or an answer it was given, and what it does
 * with one is read the same way either way.
 *
 * <p>Two sources and three things to do with one: read it for its truth, compare it, fork on it. A
 * reading that had words for some of the six would draw a table whose columns say what this
 * compiler happens to recognise rather than what the body distinguishes — and a distinction it
 * cannot name is carried as a column named by the reading that met it, which two conditions the
 * body does tell apart would share.
 *
 * <p><b>A row controls both of them, which is what makes either a subject.</b> A position is
 * written at and a dependency is stood in for. A value the model computes is neither, and a
 * condition over one stays a condition this compiler read nothing of.
 */
class ADecisionIsDrawnOnWhatARowControlsTest {

    private static final String TYPES = """
            module example.subjects

            data Customer = { id: Int }
            data Score = Int
            data Accepted
            data Rejected
            data Verdict = Accepted | Rejected
            data Known = { id: Int }
            data Unknown
            data Sighting = Known | Unknown
            """;

    /** A value the body asks the truth of is one column whichever source it came from. */
    @Test
    void aTruthOfAnInputAndOfAnAnswerAreBothColumns() {
        assertEquals(List.of("f"), truths(TYPES + """

                behavior onAnInput : (f: Bool) -> Verdict
                let onAnInput (f) = if f then Accepted else Rejected
                """, "onAnInput"));

        // Under the module that declares it: two modules may declare behaviors of one name, and an
        // identity that left the module off would hold one column for two dependencies. And with
        // which call it is, since two calls are two answers.
        List<String> answered = truths(TYPES + """

                behavior permits : (c: Customer) -> Bool

                behavior throughALet : (c: Customer) -> Verdict
                    depends on permits
                let throughALet (c, permits) = {
                    let allowed = permits(c)
                    if allowed then Accepted else Rejected
                }
                """, "throughALet");
        assertEquals(1, answered.size(), answered.toString());
        assertTrue(answered.getFirst().matches("example\\.subjects\\.permits\\(c\\)#\\d+"),
                answered.toString());
    }

    /**
     * One value asked about twice is one column.
     *
     * <p>Which is what a column is for. Written as two, a rule saying the value held and a rule
     * saying it did not would be one rule of a table that admits both — an assignment no row can be
     * written at and nothing can show impossible.
     */
    @Test
    void oneValueAskedAboutTwiceIsOneColumn() {
        List<DecisionRule> rules = DecisionReadings.readToTheEnd(TYPES + """

                behavior twice : (f: Bool, g: Bool) -> Verdict
                let twice (f, g) =
                    if f then Accepted
                    else if f then Rejected
                    else if g then Accepted
                    else Rejected
                """, "twice");

        assertEquals(List.of("f", "g"), truthsOf(rules),
                "the two values the body asks about are two columns");
        assertEquals(3, rules.size(),
                "and the way through `f` denied and `f` held is no way: " + rules);
    }

    /**
     * A truth of an input position is one column however it was spelled, and what each rule says
     * of it is the value the position holds.
     *
     * <p>The side the condition holds on is the rule that reads nothing after it, so what that
     * rule says of {@code f} is which value of {@code f} the spelling holds at: {@code f == false}
     * holding is {@code f} not holding.
     */
    @Test
    void aTruthOfAnInputIsOneColumnHoweverItIsSpelled() {
        DecisionCondition f = new DecisionCondition.ATruth(
                new DecisionSubject.AnInput(TermPath.of("f")));
        DecisionCondition g = new DecisionCondition.ATruth(
                new DecisionSubject.AnInput(TermPath.of("g")));
        for (String spelling : List.of("f", "f == true", "true == f", "f /= false",
                "Bool.not(f == false)", "Bool.not(f)", "f == false", "f /= true")) {
            boolean holdsAt = !List.of("Bool.not(f)", "f == false", "f /= true").contains(spelling);
            List<DecisionRule> rules = DecisionReadings.readToTheEnd(TYPES + """

                    behavior spelled : (f: Bool, g: Bool) -> Verdict
                    let spelled (f, g) = if %s then Accepted else if g then Accepted else Rejected
                    """.formatted(spelling), "spelled");

            assertEquals(Set.of(f, g), columnsIn(rules),
                    () -> spelling + " is the truth of f: " + columnsIn(rules));
            DecisionRule taken = rules.stream().filter(rule -> rule.consulted().size() == 1)
                    .findFirst().orElseThrow(() -> new AssertionError(spelling + ": " + rules));
            assertEquals(new DecidedCondition.Stood((DecisionCondition.ATruth) f, holdsAt),
                    taken.consulted().get(f),
                    () -> spelling + " holds where f is " + holdsAt + ": " + rules);
        }
    }

    /**
     * And asked twice in two spellings it is still one column, so the way through it held and
     * denied is no way.
     */
    @Test
    void oneValueAskedAboutTwiceInTwoSpellingsIsOneColumn() {
        List<DecisionRule> rules = DecisionReadings.readToTheEnd(TYPES + """

                behavior twice : (f: Bool, g: Bool) -> Verdict
                let twice (f, g) =
                    if f then Accepted
                    else if f == true then Rejected
                    else if g then Accepted
                    else Rejected
                """, "twice");

        assertEquals(List.of("f", "g"), truthsOf(rules),
                "the two values the body asks about are two columns");
        assertEquals(3, rules.size(),
                "and the way through `f` denied and `f == true` held is no way: " + rules);
    }

    /**
     * A comparison over an answer is the proposition it states, however it was written.
     *
     * <p>Both spellings over one answer, a name given one call: two calls are two answers, so what
     * is asked is whether one answer compared two ways is one column.
     */
    @Test
    void aComparisonOverAnAnswerIsOneProposition() {
        DecisionCondition written = onlyColumn(compares("r.value >= 700", "700 <= r.value"));
        assertEquals(written, onlyColumn(compares("r.value >= 700", "r.value + 10 >= 710")),
                "and so is the same proposition with the threshold moved");

        DecisionCondition.AComparison comparison =
                assertInstanceOf(DecisionCondition.AComparison.class, written);
        assertEquals(1, comparison.form().coefs().size(), comparison.toString());
        assertAnswerAbout("riskScore", assertInstanceOf(DecisionAtom.OfAnAnswer.class,
                comparison.form().coefs().keySet().iterator().next()).at());
    }

    /**
     * And one written with a quantity on each side is one proposition either way round.
     *
     * <p>The case a reading that keeps the authored side cannot answer. With a number on one side,
     * which quantity the author put on the left and which one this reading writes first are the
     * same quantity; with one on each side they are not, and the two spellings come out as
     * quantities that are each other negated. A table holding both admits an assignment where one
     * proposition holds and does not.
     */
    @Test
    void aComparisonOfTwoQuantitiesIsOnePropositionEitherWayRound() {
        onlyColumn(comparesTo("r.value >= limit.value", "limit.value <= r.value"));
        onlyColumn(comparesTo("r.value == limit.value", "limit.value == r.value"));
    }

    /**
     * A dependency asked about a number it was written with is an answer a row stands in.
     *
     * <p>What a row controls is what makes a distinction one an author can write a row against, and
     * what the dependency was asked about is what a row pins the answer by and a report names it
     * by: a number the model settles says that as well as a position does.
     */
    @Test
    void anAnswerAboutAWrittenNumberIsAColumn() {
        Set<DecisionCondition> columns = columnsOf(TYPES + """

                behavior riskAt : (n: Int) -> Score

                behavior once : (c: Customer) -> Verdict
                    depends on riskAt
                let once (c, riskAt) = if riskAt(42).value >= 700 then Accepted else Rejected
                """, "once");

        assertEquals(1, columns.size(), columns.toString());
        DecisionAtom asked = assertInstanceOf(DecisionCondition.AComparison.class,
                columns.iterator().next()).form().coefs().keySet().iterator().next();
        assertEquals(List.of(new DecisionArgument.OfANumber(ExactRatio.of(42))),
                assertInstanceOf(DecisionAtom.OfAnAnswer.class, asked).at().answered()
                        .arguments(), asked.toString());
    }

    /**
     * Two calls of a dependency are two answers, whatever each was asked about; a name given one
     * call is that one answer however often it is read.
     *
     * <p>A dependency is the outside world, and two calls of one need not answer alike: a counter
     * handing out the next number answers each call differently. Read as one column, the way
     * through the first call denied and the second held would be no way at all.
     */
    @Test
    void twoCallsAreTwoAnswersAndANameForOneIsOne() {
        for (List<String> asked : List.of(List.of("riskScore", "(c: Customer)", "riskScore(a)"),
                List.of("riskAt", "(n: Int)", "riskAt(42)"))) {
            assertEquals(2, columnsOf(TYPES + """

                    behavior %1$s : %2$s -> Score

                    behavior twice : (a: Customer) -> Verdict
                        depends on %1$s
                    let twice (a, %1$s) =
                        if %3$s.value >= 700 then
                            if %3$s.value >= 700 then Accepted else Rejected
                        else Rejected
                    """.formatted(asked.get(0), asked.get(1), asked.get(2)), "twice").size(),
                    asked.get(2) + " called twice is two answers");
        }

        assertEquals(1, columnsOf(TYPES + """

                behavior riskScore : (c: Customer) -> Score

                behavior named : (a: Customer) -> Verdict
                    depends on riskScore
                let named (a, riskScore) = {
                    let risk = riskScore(a)
                    let same = risk
                    if risk.value >= 700 then
                        if same.value >= 700 then Accepted else Rejected
                    else Rejected
                }
                """, "named").size(), "and one call read through two names is one answer");
    }

    /** The arms of a fork on an answer are answers about that one subject. */
    @Test
    void theArmsOfAForkOnAnAnswerShareOneSubject() {
        List<DecisionRule> rules = DecisionReadings.readToTheEnd(TYPES + """

                behavior lookUp : (c: Customer) -> Sighting

                behavior byAFork : (c: Customer) -> Verdict
                    depends on lookUp
                let byAFork (c, lookUp) =
                    match lookUp(c) with
                        | Known   -> Accepted
                        | Unknown -> Rejected
                """, "byAFork");

        Set<DecisionCondition> columns = columnsIn(rules);
        assertEquals(1, columns.size(), "one fork is one distinction: " + columns);
        DecisionCondition.ACase column =
                assertInstanceOf(DecisionCondition.ACase.class, columns.iterator().next());
        assertInstanceOf(DecisionSubject.AnAnswer.class, column.of(),
                "and it is asked of what the dependency answered");
        assertEquals(2, rules.size(), "with one rule per arm");
    }

    /**
     * A comparison over the name an arm gives what a dependency answered is the comparison over
     * the answer.
     *
     * <p>The name stands for the value that was matched, and the arm narrows nothing a row writes:
     * no position is under the call and no set of written values. Read as a name nothing could say
     * anything about, the comparison was a column this reading names when written over the call and
     * one it read nothing of when written through the arm.
     */
    @Test
    void aComparisonThroughTheNameAnArmGivesAnAnswerIsOverTheAnswer() {
        String model = TYPES + """

                data Unscored

                behavior scoreOf : (c: Customer) -> Score | Unscored

                behavior decide : (c: Customer, limit: Score) -> Verdict
                    depends on scoreOf
                let decide (c, limit, scoreOf) =
                    BODY
                """;
        Set<DecisionCondition> matched = columnsOf(model.replace("BODY", """
                match scoreOf(c) with
                        | Unscored -> Rejected
                        | Score as s -> if s.value >= limit.value then Accepted else Rejected"""),
                "decide");
        Set<DecisionCondition> throughALet = columnsOf(model.replace("BODY", """
                {
                        let found = scoreOf(c)
                        match found with
                            | Unscored -> Rejected
                            | Score as s -> if s.value >= limit.value then Accepted else Rejected
                    }"""), "decide");

        // However many names stand between the call and the arm.
        for (Set<DecisionCondition> columns : List.of(matched, throughALet)) {
            DecisionCondition.AComparison compared = columns.stream()
                    .filter(DecisionCondition.AComparison.class::isInstance)
                    .map(DecisionCondition.AComparison.class::cast).findFirst()
                    .orElseThrow(() -> new AssertionError("the comparison is a column: " + columns));
            DecisionSubject.AnAnswer answer = compared.form().coefs().keySet().stream()
                    .filter(DecisionAtom.OfAnAnswer.class::isInstance)
                    .map(atom -> ((DecisionAtom.OfAnAnswer) atom).at()).findFirst()
                    .orElseThrow(() -> new AssertionError(
                            "the comparison is over what the dependency answered: " + compared));
            assertAnswerAbout("scoreOf", answer);
            assertEquals(Set.of(new DecisionAtom.OfAnAnswer(answer),
                            new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("limit")))),
                    compared.form().coefs().keySet(),
                    "over what the dependency answered and the input it is compared with: "
                            + compared);
            assertTrue(columns.stream().anyMatch(column -> column
                            instanceof DecisionCondition.ACase fork && fork.of().equals(answer)),
                    "and over the one answer the fork is on: " + columns);
        }
    }

    /**
     * What an optional answer holds is not the answer.
     *
     * <p>{@code Some s} names what stands under the present carrier, and read as the value that was
     * matched, {@code s.value} would be a number of the optional field as a whole — a column over a
     * quantity the dependency never answered.
     */
    @Test
    void whatAnOptionalInAnAnswerHoldsIsNotTheOptional() {
        Set<DecisionCondition> columns = columnsOf(TYPES + """

                data Found = { score: Score? }

                behavior scoreOf : (c: Customer) -> Found

                behavior decide : (c: Customer, limit: Score) -> Verdict
                    depends on scoreOf
                let decide (c, limit, scoreOf) =
                    match scoreOf(c).score with
                        | None -> Rejected
                        | Some s -> if s.value >= limit.value then Accepted else Rejected
                """, "decide");

        assertTrue(columns.stream().noneMatch(column -> column
                        instanceof DecisionCondition.AComparison compared
                        && compared.form().coefs().keySet().stream()
                                .anyMatch(DecisionAtom.OfAnAnswer.class::isInstance)),
                "no comparison is over the optional the answer holds: " + columns);
    }

    /**
     * A truth of an answer is one column however it is spelled, as a truth of a position is.
     *
     * <p>{@code trusts(c) == false} holding is {@code trusts(c)} not holding. Read as two columns, a
     * body asking both would be a table that admits the answer holding and not.
     */
    @Test
    void aTruthOfAnAnswerIsOneColumnHoweverItIsSpelled() {
        for (String spelling : List.of("trusts(c)", "trusts(c) == true", "false /= trusts(c)",
                "trusts(c) == false", "trusts(c) /= true", "Bool.not(trusts(c))",
                "Bool.not(trusts(c)) == true")) {
            boolean holdsAt = !List.of("trusts(c) == false", "trusts(c) /= true",
                    "Bool.not(trusts(c))", "Bool.not(trusts(c)) == true").contains(spelling);
            List<DecisionRule> rules = DecisionReadings.readToTheEnd(TYPES + """

                    behavior trusts : (c: Customer) -> Bool

                    behavior spelled : (c: Customer) -> Verdict
                        depends on trusts
                    let spelled (c, trusts) = if %s then Accepted else Rejected
                    """.formatted(spelling), "spelled");

            DecisionCondition trusts = onlyColumn(rules);
            assertAnswerAbout("trusts",
                    assertInstanceOf(DecisionCondition.ATruth.class, trusts).of());
            DecisionRule taken = rules.getFirst();
            assertEquals(new DecidedCondition.Stood((DecisionCondition.ATruth) trusts, holdsAt),
                    taken.consulted().get(trusts),
                    () -> spelling + " holds where trusts(c) is " + holdsAt + ": " + rules);
        }
    }

    /**
     * A value the model computes is no subject, and the condition over it stays unread.
     *
     * <p>The negative control this whole reading rests on: what makes an answer a subject is that a
     * row can stand the dependency in, and nothing a row can write settles what an operation of the
     * language answers.
     */
    @Test
    void aTruthOfSomethingNoRowControlsIsNotAColumn() {
        Set<DecisionCondition> columns = columnsIn(DecisionReadings.readToTheEnd(TYPES + """

                behavior named : (c: Customer, code: String) -> Verdict
                let named (c, code) =
                    if String.startsWith("JP", code) then Accepted else Rejected
                """, "named"));

        assertEquals(1, columns.size(), columns.toString());
        assertInstanceOf(DecisionCondition.AConditionNotRead.class, columns.iterator().next(),
                "what an operation of the language answers is nothing a row pins: " + columns);
    }

    /** That {@code subject} is what {@code dependency} of this module answered when asked about
     *  {@code c}, at the answer itself — whichever call of it. */
    private static void assertAnswerAbout(String dependency, DecisionSubject subject) {
        DecisionSubject.AnAnswer answer = assertInstanceOf(DecisionSubject.AnAnswer.class, subject);
        assertEquals(new ValueName.Behavior("example.subjects", dependency),
                answer.answered().dependency(), answer.toString());
        assertEquals(List.of(new DecisionArgument.OfASubject(
                        new DecisionSubject.AnInput(TermPath.of("c")))),
                answer.answered().arguments(), answer.toString());
        assertEquals(List.of(), answer.steps(), answer.toString());
    }

    /** The columns of {@code behavior}, in the order the rules met them. */
    private static Set<DecisionCondition> columnsOf(String model, String behavior) {
        return columnsIn(DecisionReadings.readToTheEnd(model, behavior));
    }

    private static Set<DecisionCondition> columnsIn(List<DecisionRule> rules) {
        return rules.stream().flatMap(rule -> rule.consulted().keySet().stream())
                .collect(Collectors.toCollection(LinkedHashSet::new));
    }

    private static DecisionCondition onlyColumn(List<DecisionRule> rules) {
        Set<DecisionCondition> columns = columnsIn(rules);
        assertEquals(1, columns.size(), "one comparison is one column: " + columns);
        return columns.iterator().next();
    }

    /** The same, over a body whose input carries a quantity of its own to compare against. */
    private static List<DecisionRule> comparesTo(String first, String second) {
        return DecisionReadings.readToTheEnd(TYPES + """

                behavior riskScore : (c: Customer) -> Score

                behavior decide : (c: Customer, limit: Score) -> Verdict
                    depends on riskScore
                let decide (c, limit, riskScore) = {
                    let r = riskScore(c)
                    if %s then Accepted else if %s then Rejected else Accepted
                }
                """.formatted(first, second), "decide");
    }

    /** The rules of a body that decides by {@code first} and then {@code second}, both over the
     *  one answer a name {@code r} is given. */
    private static List<DecisionRule> compares(String first, String second) {
        return DecisionReadings.readToTheEnd(TYPES + """

                behavior riskScore : (c: Customer) -> Score

                behavior decide : (c: Customer) -> Verdict
                    depends on riskScore
                let decide (c, riskScore) = {
                    let r = riskScore(c)
                    if %s then Accepted else if %s then Rejected else Accepted
                }
                """.formatted(first, second), "decide");
    }

    /** What the truths of {@code behavior} are read of, in the order the reading met them. */
    private static List<String> truths(String model, String behavior) {
        return truthsOf(DecisionReadings.readToTheEnd(model, behavior));
    }

    private static List<String> truthsOf(List<DecisionRule> rules) {
        return columnsIn(rules).stream()
                .filter(DecisionCondition.ATruth.class::isInstance)
                .map(column -> ((DecisionCondition.ATruth) column).of().toString()).toList();
    }

    /** Every rule of a body that decides on nothing is one rule, which is what makes the counts
     *  above readable. */
    @Test
    void aBodyThatDecidesNothingStatesOneRule() {
        assertTrue(columnsOf(TYPES + """

                behavior flat : (c: Customer) -> Verdict
                let flat (c) = Accepted
                """, "flat").isEmpty(), "nothing is consulted");
    }
}
