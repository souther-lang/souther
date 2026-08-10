package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Ast;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.observe.Classification;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Rows for what nothing covers.
 *
 * <p>Two things are being held to here beyond the rows themselves. The same model has to produce the
 * same rows every time, or a generated block cannot be compared with the one from last week and a build
 * that prints it is noise. And a combination nothing could be written for has to come back said out
 * loud, with which of the three things happened — a generator that returned its successes and swallowed
 * the rest would read as though it had filled everything.
 */
class GeneratorTest {

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
            """;

    /** A sum whose cases are records, which is what a generator composes rather than names. */
    private static final String PAYMENT = """
            module example.pay

            data Amount = Decimal
                invariant value >= 0.0m

            data Card = { number: Amount }
            data Cash = { amount: Amount }
            data Payment = Card | Cash

            behavior feeFor : (p: Payment) -> Amount
                constructs Amount

            let feeFor (p) =
                match p with
                    | Card -> Amount(1.0m)
                    | Cash -> Amount(0.0m)
            """;

    /** An optional whose element is a record, which is the same value this composes at a parameter. */
    private static final String OPTIONAL_RECORD = """
            module example.opt

            data Amount = Decimal
                invariant value >= 0.0m

            data Card = { number: Amount }

            data Request = { card: Card? }

            behavior feeOf : (p: Request) -> Amount
                constructs Amount

            let feeOf (p) =
                match p.card with
                    | None -> Amount(0.0m)
                    | Some c -> c.number
            """;

    private record Model(Generator.Subject subject, Symbols symbols) {}

    private static Model modelOf(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Ast.Module prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Symbols symbols = compilation.db().ask(new Shapes.Scope(module)).value();
        assertNotNull(prepared);
        assertNotNull(sigs);
        Ast.SpecBehavior spec = (Ast.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals(behavior)).findFirst().orElseThrow();
        Sig sig = sigs.get(behavior);
        List<String> parameters = spec.params().stream().map(Ast.Param::name).toList();
        Partitions.Partitioning partitioning = Partitions.of(spec, sig, symbols, Exclusions.NONE);
        return new Model(new Generator.Subject(parameters, sig.inputTypes(), partitioning.axes(), symbols),
                symbols);
    }

    private static List<String> texts(Generator.GenerationResult result) {
        List<String> out = new ArrayList<>();
        for (Generator.GeneratedRow row : result.rows()) {
            out.add(String.join(", ", row.inputs().stream().map(FixtureTemplate::text).toList()));
        }
        return out;
    }

    /** Two positions of two classes is four combinations, and nothing having been written means all
     * four are still to write. */
    @Test
    void everyUncoveredCombinationGetsARow() {
        Generator.GenerationResult filled = Generator.fill(modelOf(TRIP, "submit").subject(),
                List.of(), Generator.CandidateCheck.ANY);

        assertEquals(List.of(), filled.unresolved());
        assertEquals(4, filled.rows().size(), texts(filled).toString());
        assertEquals(List.of(
                        List.of("request.kind=Domestic", "request.urgent=true"),
                        List.of("request.kind=Domestic", "request.urgent=false"),
                        List.of("request.kind=Overseas", "request.urgent=true"),
                        List.of("request.kind=Overseas", "request.urgent=false")),
                filled.rows().stream().map(Generator.GeneratedRow::classes).toList());
    }

    /** Several positions of one parameter are one value. {@code request.kind} and {@code request.urgent}
     * are two positions of one {@code Request}, and a row writes one of those. */
    @Test
    void positionsOfOneParameterCompoundIntoOneValue() {
        Generator.GenerationResult filled = Generator.fill(modelOf(TRIP, "submit").subject(),
                List.of(), Generator.CandidateCheck.ANY);

        assertEquals(1, filled.rows().get(0).inputs().size());
        assertEquals("Request { kind = Domestic, urgent = true }",
                filled.rows().get(0).inputs().get(0).text());
    }

    /** A row already written is a combination already covered, and nothing writes it twice. */
    @Test
    void whatTheRowsAlreadyReachIsNotGeneratedAgain() {
        Generator.Subject subject = modelOf(TRIP, "submit").subject();
        Map<AxisId, Classification> written = Map.of(
                new AxisId("submit", "request.kind"), Classification.in("Domestic"),
                new AxisId("submit", "request.urgent"), Classification.in("true"));

        Generator.GenerationResult filled =
                Generator.fill(subject, List.of(written), Generator.CandidateCheck.ANY);

        assertEquals(3, filled.rows().size());
        assertTrue(filled.rows().stream()
                        .noneMatch(r -> r.classes().equals(
                                List.of("request.kind=Domestic", "request.urgent=true"))),
                "the combination a row already sits in");
    }

    /** A block that changed between two runs of one model could not be compared with the last one. */
    @Test
    void theSameModelGeneratesTheSameRowsTwice() {
        Generator.GenerationResult once = Generator.fill(modelOf(TRIP, "submit").subject(),
                List.of(), Generator.CandidateCheck.ANY);
        Generator.GenerationResult again = Generator.fill(modelOf(TRIP, "submit").subject(),
                List.of(), Generator.CandidateCheck.ANY);

        assertEquals(texts(once), texts(again));
        assertEquals(once.rows().stream().map(Generator.GeneratedRow::classes).toList(),
                again.rows().stream().map(Generator.GeneratedRow::classes).toList());
    }

    // --- what a candidate says and what it does not ----------------------------------------------

    /** Two positions, each a bare number, so a hand-made class is the whole of what is at each. */
    private static Generator.Subject twoNumbers(Symbols symbols, List<PartitionClass> left,
                                                List<PartitionClass> right) {
        Axis a = new Axis(new AxisId("f", "a"), new NumericTerm.ValueOf(TermPath.of("a")), Type.INT, left,
                List.of());
        Axis b = new Axis(new AxisId("f", "b"), new NumericTerm.ValueOf(TermPath.of("b")), Type.INT, right,
                List.of());
        return new Generator.Subject(List.of("a", "b"), List.of(Type.INT, Type.INT), List.of(a, b),
                symbols);
    }

    private static PartitionClass number(String id, long... candidates) {
        List<FixtureTemplate> values = new ArrayList<>();
        for (long each : candidates) {
            values.add(FixtureTemplate.integer(each));
        }
        return PartitionClass.of(id, id, _ -> Membership.NO_MATCH, () -> values);
    }

    /**
     * A value refused at construction says nothing about the class it stood for.
     *
     * <p>Two classes covering wide ranges can have chosen representatives that break a rule relating
     * them while other values of the same two classes do not. A generator that gave up on the first
     * refusal would report a combination as unfilled that a second value fills.
     */
    @Test
    void aRefusedValueIsFollowedByTheNextOne() {
        Symbols symbols = modelOf(TRIP, "submit").symbols();
        Generator.Subject subject = twoNumbers(symbols, List.of(number("low", 1, 2)),
                List.of(number("high", 10, 20)));
        Generator.CandidateCheck refusesTheFirst = (at, candidate) ->
                candidate.text().equals("1") || candidate.text().equals("10")
                        ? Optional.of("the first pair is not allowed together") : Optional.empty();

        Generator.GenerationResult filled =
                Generator.fill(subject, List.of(), refusesTheFirst);

        assertEquals(List.of(), filled.unresolved());
        assertEquals(List.of("2, 20"), texts(filled));
    }

    /**
     * Every value refused is not a proof that the combination is impossible.
     *
     * <p>Which is why it is reported as its own reason and never lands in {@code provenInfeasible}:
     * another value of the same two classes may well build, and nothing here has tried one.
     */
    @Test
    void everyCandidateRefusedIsSaidAsItsOwnReason() {
        Symbols symbols = modelOf(TRIP, "submit").symbols();
        Generator.Subject subject = twoNumbers(symbols, List.of(number("low", 1)),
                List.of(number("high", 10)));

        Generator.GenerationResult filled =
                Generator.fill(subject, List.of(), (_, _) -> Optional.of("no"));

        assertEquals(List.of(), filled.rows());
        assertTrue(filled.unresolved().stream().allMatch(left ->
                        left.reason() == Generator.UnresolvedCombination.Reason
                                .ALL_CANDIDATES_REJECTED),
                filled.unresolved().toString());
        assertTrue(filled.unresolved().stream()
                        .anyMatch(left -> left.classes().equals(List.of("a=low", "b=high"))),
                filled.unresolved().toString());
    }

    /** A class nothing can write a value for is still a class, and the row it wants is still owed. */
    @Test
    void aClassWithNoValueIsNamedRatherThanDropped() {
        Symbols symbols = modelOf(TRIP, "submit").symbols();
        Generator.Subject subject = twoNumbers(symbols,
                List.of(PartitionClass.ungeneratable("opaque", "opaque", _ -> Membership.NO_MATCH, "no value")),
                List.of(number("high", 10)));

        Generator.GenerationResult filled =
                Generator.fill(subject, List.of(), Generator.CandidateCheck.ANY);

        assertEquals(List.of(), filled.rows());
        assertTrue(filled.unresolved().stream()
                        .anyMatch(left -> left.classes().contains("a=opaque")),
                filled.unresolved().toString());
    }

    /**
     * What could not be written names what had nothing, not the combinations that wanted it.
     *
     * <p>A position nothing can write a value for makes every combination it takes part in unfillable.
     * Saying so per combination is one fact repeated as many times as the arithmetic allows — 547 lines
     * on one model measured here — and not one of them says which position it was.
     */
    @Test
    void whatHadNoValueIsNamedRatherThanTheCombinationsThatWantedIt() {
        Symbols symbols = modelOf(TRIP, "submit").symbols();
        Generator.Subject subject = twoNumbers(symbols,
                List.of(PartitionClass.ungeneratable("opaque", "opaque", _ -> Membership.NO_MATCH, "no value"),
                        number("low", 1)),
                List.of(number("high", 10), number("higher", 20)));

        Generator.GenerationResult filled =
                Generator.fill(subject, List.of(), Generator.CandidateCheck.ANY);

        List<String> subjects = filled.unresolved().stream()
                .map(Generator.UnresolvedCombination::subject).distinct().toList();
        assertEquals(List.of("a=opaque"), subjects,
                "the class with nothing, once — not the three combinations it is in");
        assertEquals(2, filled.rows().size(), "the rest is still filled");
    }

    /**
     * A sum's record case is composed from its fields, the same as a record a parameter holds.
     *
     * <p>Nothing about it was ever unwritable: a row carrying one is a line an author writes by hand,
     * and the walk that would compose it is the one every other record goes through. What the class
     * could not do is name a value, which is a different thing from there being none — so it names
     * the constructor instead and the composition happens where composition happens.
     */
    @Test
    void aRecordCaseOfASumIsComposedFromItsFields() {
        Generator.GenerationResult filled = Generator.fill(modelOf(PAYMENT, "feeFor").subject(),
                List.of(), Generator.CandidateCheck.ANY);

        assertEquals(List.of(), filled.unresolved(), filled.unresolved().toString());
        assertEquals(List.of("Card { number = Amount(0m) }", "Cash { amount = Amount(0m) }"),
                texts(filled));
    }

    /**
     * A class that recorded why nothing was composed for it is not reported as one nothing can be
     * written for.
     *
     * <p>The two license different work. "No value can be written there" tells an author the row does
     * not exist; what a record case has is a value this composes everywhere else and does not compose
     * here, which is a row they can write by hand in one line. The class already says which of the two
     * it is, at the point it is built.
     */
    @Test
    void aClassThatSaidWhyNothingWasComposedIsNotReportedAsHavingNoValue() {
        Generator.GenerationResult filled = Generator.fill(
                modelOf(OPTIONAL_RECORD, "feeOf").subject(), List.of(),
                Generator.CandidateCheck.ANY);

        Generator.UnresolvedCombination some = filled.unresolved().stream()
                .filter(each -> each.classes().contains("p.card=Some")).findFirst().orElseThrow();
        assertEquals(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, some.reason(),
                "a value this could not compose, not one that cannot exist");
        assertTrue(some.said().isPresent(), "the reason the class recorded");
        assertEquals("p.card=Some", some.subject(),
                "the position, which is what several of these share");
    }

    /**
     * What a class records about itself does not claim the value cannot be written either.
     *
     * <p>The sentence is the whole of what an author gets, so moving the overclaim out of the reason
     * and into the words beside it would change nothing. Nothing that ends at an empty list has
     * established that a value does not exist: {@code Option<Card>} has one, spelled the way the row
     * above spells a record.
     */
    @Test
    void whatAClassRecordsDoesNotClaimTheValueCannotBeWritten() {
        Generator.GenerationResult filled = Generator.fill(modelOf(OPTIONAL_RECORD, "feeOf").subject(),
                List.of(), Generator.CandidateCheck.ANY);

        Generator.UnresolvedCombination some = filled.unresolved().stream()
                .filter(each -> each.classes().contains("p.card=Some")).findFirst().orElseThrow();
        String said = some.said().orElse("");
        assertTrue(said.contains("Card"), "which value it was about, which is " + said);
        assertFalse(said.contains("can be written"),
                "an empty list is not a value that cannot be written: " + said);
    }

    /**
     * One divided position has no pairs at all, and still owes a row for each of its classes.
     *
     * <p>Which is why the two are counted separately rather than one derived from the other. A
     * generator that only filled pairs would write nothing here and leave a report saying a class
     * nothing reaches, with no way to act on it.
     */
    @Test
    void onePositionHasNoPairsAndItsClassesStillOweRows() {
        Symbols symbols = modelOf(TRIP, "submit").symbols();
        Axis only = new Axis(new AxisId("f", "a"), new NumericTerm.ValueOf(TermPath.of("a")), Type.INT,
                List.of(number("low", 1), number("high", 9)), List.of());
        Generator.Subject subject = new Generator.Subject(List.of("a"), List.of(Type.INT),
                List.of(only), symbols);

        Generator.GenerationResult filled =
                Generator.fill(subject, List.of(), Generator.CandidateCheck.ANY);

        assertEquals(List.of("1", "9"), texts(filled));
        assertEquals(List.of(List.of("a=low"), List.of("a=high")),
                filled.rows().stream().map(Generator.GeneratedRow::classes).toList());
    }
}
