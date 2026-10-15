package souther.compiler.partition;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.meaning.Proposition;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A condition whose meaning follows from the rules the reading has, put together, is read whole:
 * no part of it is left unread for want of putting them together.
 *
 * <p>One behavior for each way the rules are put together. A value chosen by cases is read on each
 * case wherever it stands — added to a number, under a field of what each case builds, handed to an
 * operation, as what a container holds. A behavior a call names, and no row stands in, is read
 * through its body where the call stands, whether it answers a truth or a number, or is handed to
 * an operation as its closure. A dependency asked about a value the body works out is the answer a
 * row stands in, named by how the value was worked out. A value written out that reads names of
 * its own is read where it was written, and a name standing for one of several values written out
 * — what a walk answered over them, among others — is read on each of them. A match on an optional
 * an operation answered selects by whether it holds a value, which is that operation's law. And
 * some element of a walk's answer, one value per element, is the step's answer on some element of
 * what it walked.
 *
 * <p>Each is read to the end, and a few say what they come to, so a reading that gave up on the way
 * and one that came out somewhere else are both told from the reading these hold.
 */
class WhatTheRulesComposeIsReadWholeTest {

    private static final String MODEL = """
            module m

            data Line = { price: Int, paid: Bool }
            data Order = { lines: List<Line>, floor: Int, ceil: Int, maybe: Option<Int>, name: String }

            let pick (o: Order): Int = if o.floor > 3 then 1 else 2

            behavior big : (n: Int) -> Bool
            let big (n) = n > 3

            behavior twice : (n: Int) -> Int
            let twice (n) = n + n

            behavior bigLine : (l: Line) -> Bool
            let bigLine (l) = l.price > 3

            behavior known : (s: String) -> Bool

            behavior aChoiceAddedToANumber : (o: Order) -> Int
            let aChoiceAddedToANumber (o) = {
                let c = if o.floor > 3 then 1 else 2
                if c + o.ceil > 4 then 1 else 2
            }

            behavior aChoiceAHelperMakes : (o: Order) -> Int
            let aChoiceAHelperMakes (o) = if pick(o) + o.ceil > 4 then 1 else 2

            behavior anOperationDefinedByCasesInANumber : (o: Order) -> Int
            let anOperationDefinedByCasesInANumber (o) = if Int.max(o.floor, o.ceil) + 1 > 4 then 1 else 2

            behavior aFieldOfWhatEachCaseBuilds : (o: Order) -> Int
            let aFieldOfWhatEachCaseBuilds (o) = {
                let c = match o.maybe with
                    | Some n -> Line { price = n, paid = true }
                    | None -> Line { price = 3, paid = false }
                if o.floor <= c.price then 1 else 2
            }

            behavior aChoiceHandedToAnOperation : (o: Order) -> Int
            let aChoiceHandedToAnOperation (o) = if List.isEmpty(List.take(if o.floor > 3 then 1 else 0, o.lines)) then 1 else 2

            behavior howManyAChosenContainerHolds : (o: Order) -> Int
            let howManyAChosenContainerHolds (o) = if List.length(if o.floor > 3 then o.lines else []) > 2 then 1 else 2

            behavior aBehaviorsTruth : (o: Order) -> Int
            let aBehaviorsTruth (o) = if big(o.floor + 1) then 1 else 2

            behavior aBehaviorsNumber : (o: Order) -> Int
            let aBehaviorsNumber (o) = if twice(o.floor) > 4 then 1 else 2

            behavior aBehaviorAsAClosure : (o: Order) -> Int
            let aBehaviorAsAClosure (o) = if List.all(bigLine, o.lines) then 1 else 2

            behavior aDependencyAskedAboutAValueWorkedOut : (o: Order) -> Int
                depends on known
            let aDependencyAskedAboutAValueWorkedOut (o, known) = if known(String.lowercase(o.name)) then 1 else 2

            behavior aValueWrittenOutReadingANameOfItsOwn : (o: Order) -> Int
            let aValueWrittenOutReadingANameOfItsOwn (o) = {
                let y = o.floor + o.ceil
                if List.any(x -> x > 3, [y, 2]) then 1 else 2
            }

            behavior aMatchOnWhatAnOperationAnswered : (o: Order) -> Int
            let aMatchOnWhatAnOperationAnswered (o) = match List.find(l -> l.price > o.floor, o.lines) with
                | Some v -> 1
                | None -> 2

            behavior aWalkOverValuesWrittenOut : (o: Order) -> Int
            let aWalkOverValuesWrittenOut (o) = if List.any(y -> y > 3, List.map(x -> x + o.floor, [1, 2])) then 1 else 2

            behavior aWalkOverAPosition : (o: Order) -> Int
            let aWalkOverAPosition (o) = if List.any(y -> y > 3, List.map(l -> l.price, o.lines)) then 1 else 2
            """;

    /** The behaviors the others call, which are read where they are called. */
    private static final Set<String> CALLED = Set.of("big", "twice", "bigLine");

    /** What reading each behavior takes: its body, where its names are read, and its input. */
    private record Read(AnalysisBody body, InputReads reads, InputReading input,
                        MeaningsOfABody meanings) {}

    private static final Map<String, Read> READ = new LinkedHashMap<>();

    @BeforeAll
    static void read() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code() + " " + each.diagnostic().titleKey())
                        .toList(),
                "the model compiles");
        String module = compilation.modules().getFirst();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        Map<String, InputDomain> inputs = compilation.db().ask(new Adequacy.Inputs(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        inputs.forEach((behavior, input) -> {
            AnalysisBody analysis = checked.analysisBodies().get(behavior);
            if (analysis == null || CALLED.contains(behavior)) {
                return;
            }
            InputReading reading = input.reading(rules);
            InputReads reads = InputReads.ofParametersWhereCallsStand(input.parameterReads(),
                    input.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                    input.dependencies());
            READ.put(behavior, new Read(analysis, reads, reading, MeaningsOfABodyReading.of(
                    analysis, () -> reading, reads, rules.symbols(), rules.newtypes())));
        });
    }

    @Test
    void everyConditionIsReadToTheEnd() {
        assertEquals(14, READ.size(), "a behavior for each way the rules are put together");
        READ.forEach((behavior, read) -> {
            assertFalse(read.meanings().stated().isEmpty(), () -> behavior + " has conditions");
            read.meanings().stated().forEach((site, meaning) -> assertEquals(List.of(),
                    Proposition.stopsIn(meaning.states()),
                    () -> behavior + " leaves a part of " + meaning.states().key() + " unread"));
        });
    }

    /** What a few of them come to: the condition of the fork the body is. */
    @Test
    void whatTheyComeTo() {
        assertEquals("Affine[form=LinearForm[constant=-2, coefs={o.floor=1}], proposition=GT]",
                forkOf("aBehaviorsTruth"), "the body's n > 3 with o.floor + 1 for n");
        assertEquals("Affine[form=LinearForm[constant=-4, coefs={o.floor=2}], proposition=GT]",
                forkOf("aBehaviorsNumber"), "n + n, with o.floor for n, above 4");
        assertEquals("all[Affine[form=LinearForm[constant=-2, coefs={List.length(o.lines)=1}],"
                        + " proposition=GT], Affine[form=LinearForm[constant=-3,"
                        + " coefs={o.floor=1}], proposition=GT]]",
                forkOf("howManyAChosenContainerHolds"),
                "the lines where o.floor > 3, and nought otherwise, which is never above 2");
        assertEquals("m.known(String.lowercase[o.name])#2",
                forkOf("aDependencyAskedAboutAValueWorkedOut"),
                "the answer, named by the lowercased name it was asked about");
        assertEquals("Affine[form=LinearForm[constant=-3, coefs={o.ceil=1, o.floor=1}],"
                        + " proposition=GT]",
                forkOf("aValueWrittenOutReadingANameOfItsOwn"),
                "o.floor + o.ceil above 3, the one value written out that can be");
        assertEquals("any[Affine[form=LinearForm[constant=-1, coefs={o.floor=1}],"
                        + " proposition=GT], Affine[form=LinearForm[constant=-2,"
                        + " coefs={o.floor=1}], proposition=GT]]",
                forkOf("aWalkOverValuesWrittenOut"), "1 + o.floor or 2 + o.floor above 3");
        assertEquals("some o.lines [Affine[form=LinearForm[constant=-3,"
                        + " coefs={o.lines[*].price=1}], proposition=GT]]",
                forkOf("aWalkOverAPosition"), "some line's price above 3");
    }

    /** What the condition of the fork {@code behavior}'s body is states, as a key. */
    private static String forkOf(String behavior) {
        Read read = READ.get(behavior);
        InputReads reads = read.reads();
        Core e = Core.withoutStanding(read.body().core());
        while (e instanceof Core.LetIn let) {
            reads = reads.and(let.binder(), let.value());
            e = Core.withoutStanding(let.body());
        }
        Core.If fork = assertInstanceOf(Core.If.class, e, behavior + " is one fork");
        return Pullback.ofATruth(fork.cond(), reads, read.input(), Optional.empty())
                .proposition().key();
    }
}
