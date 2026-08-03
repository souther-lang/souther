package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Rows generated against a model that really compiles, and put through the decoders that model derives.
 *
 * <p>Which is the part a generator cannot work out on its own. Whether two values are allowed together
 * is what an invariant relating two fields says, and the only way to find out is to build the value the
 * way a row's own fixture is built.
 */
class CompileExampleGenerateTest {

    private static final String TRIP = """
            module example.trip

            data Domestic
            data Overseas
            data Kind = Domestic | Overseas

            data Request = { kind: Kind, urgent: Bool }

            data Accepted = { at: String }

            behavior submit : (request: Request) -> Accepted
                constructs Accepted

            let submit (request) = Accepted { at = "now" }

            example submit
                | (Request { kind = Domestic, urgent = true }) -> Accepted { at = "now" }
            """;

    private static Map<String, Adequacy.Filling> generated(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        // What `souther examples` asks for. A line a `guard` drew is only decidable where the arms
        // were measured, so below this the generator has nothing to say about one.
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all = compilation.db()
                .ask(new Adequacy.Generated(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        return all;
    }

    private static List<String> inputs(Generator.GenerationResult result) {
        return result.rows().stream()
                .map(r -> String.join(", ",
                        r.inputs().stream().map(i -> i.text()).toList()))
                .toList();
    }

    @Test
    void whatTheWrittenRowAlreadyCoversIsNotGeneratedAgain() {
        Generator.GenerationResult filled = generated(TRIP).get("submit").pairs();

        assertEquals(List.of(
                        "Request { kind = Domestic, urgent = false }",
                        "Request { kind = Overseas, urgent = true }",
                        "Request { kind = Overseas, urgent = false }"),
                inputs(filled));
        assertEquals(List.of(), filled.unresolved());
    }

    /**
     * A rule relating two fields refuses a value each field would have allowed on its own.
     *
     * <p>Here the low end may not be above the high end. Each position on its own admits the values
     * that break it — the classes are drawn by the behavior's own comparisons and know nothing of each
     * other — so the only thing that can say the pair is not allowed is the decoder the model derives.
     * What comes back is the reason it was refused, not a claim that the combination is impossible.
     */
    @Test
    void aRuleRelatingTwoFieldsRefusesTheValueAndIsSaidSo() {
        String correlated = """
                module example.trip

                data Amount = Int
                    invariant value >= 0

                data Request = { lo: Amount, hi: Amount }
                    invariant lo.value <= hi.value

                data Accepted = { at: String }

                behavior submit : (request: Request) -> Accepted
                    constructs Accepted

                let submit (request) = {
                    guard request.lo.value <= 100 else Accepted { at = "wide" }
                    guard request.hi.value <= 50 else Accepted { at = "tall" }
                    Accepted { at = "now" }
                }
                """;
        Generator.GenerationResult filled = generated(correlated).get("submit").pairs();

        assertTrue(inputs(filled).stream().noneMatch(row -> row.contains("Amount(101)")),
                "a value the model refuses is not written into a row: " + inputs(filled));
        // Both combinations the low end's upper class takes part in, and the class on its own.
        assertEquals(3, filled.unresolved().size(), filled.unresolved().toString());
        for (Generator.UnresolvedCombination left : filled.unresolved()) {
            assertEquals(Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED,
                    left.reason());
            assertTrue(left.classes().contains("request.lo=100 < x"),
                    left.classes().toString());
        }
        // The second of the two is the reason this reason exists. A low end past 100 and a high end
        // past 50 is a combination values exist for — 101 and 200 — and the representatives the
        // classes offered happened not to be a pair that builds. Calling that impossible would take a
        // combination somebody can write a row for out of the denominator.
        assertTrue(filled.unresolved().stream()
                        .anyMatch(left -> left.classes().contains("request.hi=50 < x")),
                filled.unresolved().toString());
    }

    /**
     * A boundary is a row of its own, apart from the rows that fill the classes.
     *
     * <p>The two ask different things. A class wants any value inside it; an edge wants exactly the
     * value the rule was written at, and a row that sat on three edges at once would be three answers
     * an author has to separate.
     */
    @Test
    void aBoundaryNothingReachedGetsARowOfItsOwn() {
        String bounded = """
                module example.trip

                data Amount = Int
                    invariant value >= 0 && value <= 1000

                data Domestic
                data Overseas
                data Kind = Domestic | Overseas

                data Request = { kind: Kind, cost: Amount }

                data Accepted = { at: String }

                behavior submit : (request: Request) -> Accepted
                    constructs Accepted

                let submit (request) = Accepted { at = "now" }
                """;
        Adequacy.Filling filling = generated(bounded).get("submit");

        assertEquals(List.of("Request { kind = Domestic, cost = Amount(0) }",
                        "Request { kind = Overseas, cost = Amount(0) }"),
                inputs(filling.pairs()), "the classes, at whatever cost builds");
        assertEquals(List.of("Request { kind = Domestic, cost = Amount(0) }",
                        "Request { kind = Domestic, cost = Amount(1000) }"),
                inputs(filling.boundaries()), "the edges, at exactly the value the rule names");
    }

    /**
     * A line a `guard` drew is offered, not only named.
     *
     * <p>Writing the row and meeting the line are different questions, and only the second needs the
     * arms — but the row to write is the same row either way. A boundary the report names as unmet and
     * the generator will not offer is the one place an author is told about a gap and left to close it
     * by hand.
     */
    @Test
    void aGuardsLineIsOfferedAsWellAsNamed() {
        String guarded = """
                module example.trip

                data Amount = Int
                    invariant value >= 0

                data Draft = { cost: Amount }
                data Submitted = { cost: Amount }
                data Waiting = { cost: Amount }

                behavior submit : (request: Draft) -> Submitted | Waiting
                    constructs Submitted, Waiting

                let submit (request) = {
                    guard request.cost.value <= 100 else Waiting { cost = request.cost }
                    Submitted { cost = request.cost }
                }

                example submit
                    | (Draft { cost = Amount(50) })  -> Submitted { cost = Amount(50) }
                    | (Draft { cost = Amount(500) }) -> Waiting { cost = Amount(500) }
                """;

        assertEquals(List.of("Draft { cost = Amount(0) }",
                        "Draft { cost = Amount(100) }",
                        "Draft { cost = Amount(101) }"),
                inputs(generated(guarded).get("submit").boundaries()),
                "the invariant's edge and both sides of the guard's line");
    }

    /**
     * A value a format rule accepts, and one the model then builds.
     *
     * <p>An identifier saying what it looks like is the commonest rule there is, and nothing could
     * write one — so a record holding an id could not be composed at all, and every combination that
     * record took part in came back as one whose values the model refused. What settles this is not
     * that the string looks right but that the derived decoder takes it, which is what the check here
     * is: the row is offered only if it built.
     */
    @Test
    void anIdentifierWithAFormatRuleGetsAValueTheModelAccepts() {
        String formatted = """
                module example.office

                data OfficeId = String
                    invariant String.matches("[0-9]{2}-[0-9]{6}", value)

                data Prefecture = String
                    invariant String.matches("0[1-9]|[1-3][0-9]|4[0-7]", value)

                data Domestic
                data Overseas
                data Kind = Domestic | Overseas

                data Office = { id: OfficeId, prefecture: Prefecture, kind: Kind }
                data Ok = { n: Int }

                behavior register : (office: Office) -> Ok
                    constructs Ok

                let register (office) = Ok { n = 0 }

                example register
                    | (Office { id = OfficeId("12-345678"), prefecture = Prefecture("13"),
                                kind = Domestic }) -> Ok { n = 0 }
                """;

        assertEquals(List.of(
                        "Office { id = OfficeId(\"00-000000\"), prefecture = Prefecture(\"01\"),"
                                + " kind = Overseas }"),
                inputs(generated(formatted).get("register").pairs()),
                "the class nothing covers, with an id and a prefecture the rules accept");
    }

    /** And a date, which a row writes as its ISO form. */
    @Test
    void aDateGetsAValueTheModelAccepts() {
        String dated = """
                module example.dated

                data Yes
                data No
                data Flag = Yes | No

                data Request = { on: Date, flag: Flag }
                data Ok = { n: Int }

                behavior take : (request: Request) -> Ok
                    constructs Ok

                let take (request) = Ok { n = 0 }

                example take
                    | (Request { on = Date("2026-08-03"), flag = Yes }) -> Ok { n = 0 }
                """;

        assertEquals(List.of("Request { on = Date(\"2000-01-01\"), flag = No }"),
                inputs(generated(dated).get("take").pairs()));
    }

    /**
     * A value carrying a character a literal has to escape.
     *
     * <p>The row is text somebody pastes, so what it says has to read back as what it was made from.
     * Written as itself, a tab is invisible in the row and a newline ends it — the rest of the row
     * lands on a line that is not commented out, and what was pasted is not what was offered. So this
     * asks the compiler rather than the text: the block goes back in, and the rows have to hold.
     */
    @Test
    void aValueWithACharacterALiteralEscapesSurvivesBeingPasted() {
        String tabbed = """
                module example.tabbed

                data Spaced = String
                    invariant String.matches("a[\\\\t]b", value)

                data Yes
                data No
                data Flag = Yes | No

                data Note = { text: Spaced, flag: Flag }
                data Ok = { n: Int }

                behavior take : (note: Note) -> Ok
                    constructs Ok

                let take (note) = Ok { n = 0 }

                example take
                    | (Note { text = Spaced("a\\tb"), flag = Yes }) -> Ok { n = 0 }
                """;

        assertEquals(List.of("Note { text = Spaced(\"a\\tb\"), flag = No }"),
                inputs(generated(tabbed).get("take").pairs()),
                "the tab is written the way a literal spells one");

        String block = GeneratedRows.of("example.tabbed", generated(tabbed), false);
        String pasted = tabbed + block.lines()
                .filter(line -> line.startsWith("//     ") || line.equals("// example take"))
                .map(line -> line.substring("// ".length()).replace("<?>", "Ok { n = 0 }"))
                .reduce("", (all, line) -> all + line + "\n");

        Compilation compilation = Compilation.ofSource(pasted, "Main");
        compilation.answerEverything();
        List<souther.compiler.observe.RowOutcome> rows = outcomes(compilation);

        assertEquals(2, rows.size(), "the row that was there, and the one generated");
        for (souther.compiler.observe.RowOutcome row : rows) {
            assertEquals(souther.compiler.observe.Disposition.HELD, row.disposition(),
                    row.description() + " -> " + row.failurePhase());
        }
    }

    /** A model where the position under test is a field of the input and one flag divides the rows. */
    private static String withField(String declarations, String field) {
        return """
                module example.candidates

                %s

                data Yes
                data No
                data Flag = Yes | No

                data Req = { v: %s, f: Flag }
                data Ok = { n: Int }

                behavior take : (r: Req) -> Ok
                    constructs Ok

                let take (r) = Ok { n = 0 }

                example take
                    | (Req { v = %s, f = Yes }) -> Ok { n = 0 }
                """.formatted(declarations, field, "%s");
    }

    /**
     * A rule this cannot read leaves the position what it had.
     *
     * <p>Reading a format rule is a way to offer a value, not a way to decide there is none. A lookahead
     * is past what the reader understands, and the plain representative for the position — which built
     * before any of this existed, and which this rule happens to accept — is still offered.
     */
    @Test
    void unsupportedPatternThatAcceptsTheDefaultCandidateStillGenerates() {
        String source = withField("""
                data V = String
                    invariant String.matches("(?=x)x", value)""", "V").formatted("V(\"x\")");

        assertEquals(List.of("Req { v = V(\"x\"), f = No }"),
                inputs(generated(source).get("take").pairs()));
    }

    /**
     * Two rules on one position, in either order.
     *
     * <p>Every clause of an invariant has to hold, so the order they are written in cannot decide
     * whether a value can be found. Each readable rule contributes a candidate and the constructor
     * settles which of them stands — reading only the first would make `[a-z]+` before `x+` produce
     * `"a"` and stop, and the same two rules the other way round produce a value.
     */
    @Test
    void conjoinedPatternsDoNotDependOnDeclarationOrder() {
        String forwards = withField("""
                data V = String
                    invariant String.matches("[a-z]+", value)
                    invariant String.matches("x+", value)""", "V").formatted("V(\"x\")");
        String backwards = withField("""
                data V = String
                    invariant String.matches("x+", value)
                    invariant String.matches("[a-z]+", value)""", "V").formatted("V(\"x\")");

        assertEquals(List.of("Req { v = V(\"x\"), f = No }"),
                inputs(generated(forwards).get("take").pairs()));
        assertEquals(inputs(generated(forwards).get("take").pairs()),
                inputs(generated(backwards).get("take").pairs()),
                "the same two rules, written the other way round");
    }

    /**
     * Two positions, each needing a different one of the values it was offered.
     *
     * <p>What has to build is the whole input at once — the check is the model's own constructor — so
     * what is being tried is the tuple, not a value. Here the two positions carry the same two rules
     * written the other way round, so their values come out in opposite orders and the assignment that
     * builds is the first value of one with the second of the other. Trying one index across every
     * position walks the diagonal of the choices and never reaches it.
     */
    @Test
    void candidatesAtDifferentPositionsAreNotWalkedInLockstep() {
        String source = """
                module example.lock

                data Left = String
                    invariant String.matches("[a-z]+", value)
                    invariant String.matches("x+", value)

                data Right = String
                    invariant String.matches("x+", value)
                    invariant String.matches("[a-z]+", value)

                data Yes
                data No
                data Flag = Yes | No

                data Req = { left: Left, right: Right, flag: Flag }
                data Ok = { n: Int }

                behavior take : (request: Req) -> Ok
                    constructs Ok

                let take (request) = Ok { n = 0 }

                example take
                    | (Req { left = Left("x"), right = Right("x"), flag = Yes }) -> Ok { n = 0 }
                """;

        assertEquals(List.of("Req { left = Left(\"x\"), right = Right(\"x\"), flag = No }"),
                inputs(generated(source).get("take").pairs()));
        // And the same model with one of the two rewritten to declare its rules in the other order,
        // which is the same model. Order decided this before the assignments were walked as tuples.
        assertEquals(inputs(generated(source).get("take").pairs()),
                inputs(generated(source.replace("module example.lock", "module example.lock2")
                        .replace("""
                                data Right = String
                                    invariant String.matches("x+", value)
                                    invariant String.matches("[a-z]+", value)""", """
                                data Right = String
                                    invariant String.matches("[a-z]+", value)
                                    invariant String.matches("x+", value)""")).get("take").pairs()));
    }

    /**
     * A search that stopped says so, rather than saying everything was refused.
     *
     * <p>The choices multiply, so a row is tried at a bounded number of assignments. Past that bound
     * the ones not reached were not refused — nothing was written and nothing built — and calling them
     * refused tells an author their model rules out a combination it does not.
     */
    @Test
    void whatTheSearchDidNotReachIsNotReportedAsRefused() {
        StringBuilder declarations = new StringBuilder();
        StringBuilder fields = new StringBuilder();
        for (char c = 'a'; c <= 'i'; c++) {
            declarations.append("""
                    data V%1$s = String
                        invariant String.matches("[a-z]+", value)
                        invariant String.matches("x+", value)

                    """.formatted(Character.toUpperCase(c)));
            fields.append(c).append(": V").append(Character.toUpperCase(c)).append(", ");
        }
        String source = """
                module example.wide

                %sdata Yes
                data No
                data Flag = Yes | No

                data Req = { %sflag: Flag }
                    invariant String.length(a.value) > 1000

                data Ok = { n: Int }

                behavior take : (request: Req) -> Ok
                    constructs Ok

                let take (request) = Ok { n = 0 }
                """.formatted(declarations, fields);

        List<Generator.UnresolvedCombination> left = generated(source).get("take").pairs()
                .unresolved();

        assertFalse(left.isEmpty(), "nothing builds, so something is left");
        for (Generator.UnresolvedCombination each : left) {
            assertEquals(Generator.UnresolvedCombination.Reason.SEARCH_LIMIT, each.reason(),
                    each.toString());
            assertTrue(each.subject().startsWith("request.flag="),
                    "and it is still about the combination: " + each.subject());
        }
    }

    /**
     * A newtype's rules are read wherever it is asked for a value.
     *
     * <p>A newtype is asked for one from two places — a field of a record, and a case of a sum — and
     * the rules on it are the same rules in both. Read in only one of them, a formatted identifier
     * composes as a field and is refused as a case, which is the same model reporting a position as
     * unfillable depending on where it was written.
     */
    @Test
    void aFormattedNewtypeUsedAsASumCaseGetsARepresentative() {
        String source = """
                module example.cases

                data Email = String
                    invariant String.matches("[a-z]+@[a-z]+", value)

                data Amount = Int
                    invariant value >= 100

                data NoContact
                data Contact = Email | NoContact
                data NoAmount
                data Wallet = NoAmount | Amount

                data Req = { contact: Contact, w: Wallet }
                data Ok = { n: Int }

                behavior take : (r: Req) -> Ok
                    constructs Ok

                let take (r) = Ok { n = 0 }

                example take
                    | (Req { contact = NoContact, w = NoAmount }) -> Ok { n = 0 }
                """;

        List<String> rows = inputs(generated(source).get("take").pairs());

        assertTrue(rows.stream().anyMatch(r -> r.contains("Email(\"a@a\")")),
                "a case whose rule states a format: " + rows);
        assertTrue(rows.stream().anyMatch(r -> r.contains("Amount(100)")),
                "and one whose rule states a bound: " + rows);
    }

    // --- the block, put back through the compiler ------------------------------------------------

    /** The rows of the block, with the placeholder answered the way an author answers it. */
    private static String answered(String source, String expected) {
        String block = GeneratedRows.of("example.trip", generated(source), false);
        String rows = block.lines()
                .filter(line -> line.startsWith("//     ") || line.equals("// example submit"))
                .map(line -> line.substring("// ".length()).replace("<?>", expected))
                .reduce("", (all, line) -> all + line + "\n");
        return source + rows;
    }

    /** The rows a source's examples left, across every file that writes one. */
    private static List<souther.compiler.observe.RowOutcome> outcomes(Compilation compilation) {
        List<souther.compiler.observe.RowOutcome> rows = new ArrayList<>();
        for (String name : compilation.modules()) {
            for (String sourceId : compilation.exampleSourcesOf(name)) {
                souther.compiler.query.Output.Examples.Of observed = compilation.db()
                        .ask(new souther.compiler.query.Output.Examples(name, sourceId)).value();
                if (observed != null) {
                    rows.addAll(observed.rows());
                }
            }
        }
        return rows;
    }

    /**
     * Answered, the block is rows that hold, and what they were generated for is covered.
     *
     * <p>The whole claim about a generated row, put to the compiler rather than to the text: it parses,
     * the inputs build, the behavior takes them, the answer written against them is the one it gives,
     * and afterwards there is nothing left to generate. A row that only looked right would pass none of
     * those.
     */
    @Test
    void answeringTheBlockGivesRowsThatHoldAndCoverWhatTheyWereFor() {
        String source = answered(TRIP, "Accepted { at = \"now\" }");

        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        List<souther.compiler.observe.RowOutcome> rows = outcomes(compilation);

        assertEquals(4, rows.size(), "the row that was there, and the three generated");
        for (souther.compiler.observe.RowOutcome row : rows) {
            assertEquals(souther.compiler.observe.Disposition.HELD, row.disposition(),
                    row.description() + " -> " + row.failurePhase());
        }
        assertEquals("", GeneratedRows.of("example.trip", generated(source), false),
                "nothing is left to fill");
    }

    /** And the check above is not vacuous: a row answered with something the behavior does not give
     * fails, so the rows holding is the block's doing and not the compiler's indifference. */
    @Test
    void aRowAnsweredWrongDoesNotHold() {
        String wrong = answered(TRIP, "Accepted { at = \"later\" }");

        Compilation compilation = Compilation.ofSource(wrong, "Main");
        compilation.answerEverything();

        assertTrue(outcomes(compilation).stream()
                        .anyMatch(row -> row.disposition() == souther.compiler.observe.Disposition
                                .FAILED),
                "a wrong answer is a failing row");
    }

    /**
     * Pasted as it comes, the block changes nothing.
     *
     * <p>Which is what being commented out means, said as something the compiler can answer. A row that
     * compiled would be an assertion nobody made, and the next build would hold the model to it.
     */
    @Test
    void theBlockPastedUnchangedLeavesTheModelWhereItWas() {
        String block = GeneratedRows.of("example.trip", generated(TRIP), false);
        String pasted = TRIP + block;

        Compilation compilation = Compilation.ofSource(pasted, "Main");
        compilation.answerEverything();

        assertEquals(1, outcomes(compilation).size(), "no row was added");
        assertEquals(block, GeneratedRows.of("example.trip", generated(pasted), false),
                "the same rows are still owed");
    }

    /**
     * The rows come out in the form {@code souther fmt} writes them.
     *
     * <p>These lines are meant to be pasted into a file the formatter then runs over. A block in a
     * shape the formatter would change turns a paste into a diff on the next commit.
     */
    @Test
    void thePastedRowsSurviveFormattingUnchanged() {
        String source = answered(TRIP, "Accepted { at = \"now\" }");
        String formatted = souther.compiler.fmt.Formatter.format(source);

        for (String line : source.substring(TRIP.length()).lines().toList()) {
            assertTrue(formatted.contains(line + "\n"), line + "\n---\n" + formatted);
        }
    }

    /** Nothing to fill is nothing printed, rather than a header over an empty list. */
    @Test
    void aModelTheRowsCoverPrintsNothing() {
        String covered = TRIP + """
                    | (Request { kind = Domestic, urgent = false }) -> Accepted { at = "now" }
                    | (Request { kind = Overseas, urgent = true }) -> Accepted { at = "now" }
                    | (Request { kind = Overseas, urgent = false }) -> Accepted { at = "now" }
                """;

        assertEquals("", GeneratedRows.of("example.trip", generated(covered), false));
    }
}
