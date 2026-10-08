package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.meaning.Proposition;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A closure applied to each of the values a container was written with is read on each application,
 * the parameter handed one of them: what some element meets is some one of what the body states on
 * those applications, and a condition in the body states, on the application a run meets it on,
 * that application's statement.
 *
 * <p>Held against the values written out by hand — the disjunction or conjunction an author could
 * have written instead — since that one is read by the rules for joining truths and for comparing
 * numbers alone, and the two coming to one proposition is what says nothing was added or dropped by
 * handing the values over.
 */
class AConditionOverValuesWrittenOutIsReadOnEachApplicationTest {

    private static final String INPUT = """
            data Month = { days: Int }
            data Window = { first: Month, second: Month, third: Month, n: Int }
            """;

    @Test
    void someElementMeetingIsSomeValueWrittenOutMeetingIt() {
        assertEquals(stated("w.first.days > 3 || w.second.days > 3"),
                stated("List.any(m -> m.days > 3, [w.first, w.second])"));
        assertEquals(stated("w.first.days >= 17 || w.second.days >= 17 || w.third.days >= 17"),
                stated("List.length(List.filter(m -> m.days >= 17,"
                        + " [w.first, w.second, w.third])) >= 1"));
    }

    @Test
    void everyElementMeetingIsEveryValueWrittenOutMeetingIt() {
        assertEquals(stated("w.first.days > 3 && w.second.days > 3"),
                stated("List.all(m -> m.days > 3, [w.first, w.second])"));
    }

    /** A value written out that names nothing is itself on the application that hands it. */
    @Test
    void numbersWrittenOutAreHandedAsThemselves() {
        assertEquals(stated("w.n > 1 || w.n > 2"),
                stated("List.any(x -> w.n > x, [1, 2])"));
    }

    /**
     * A condition in the body states one thing on each application, and fails where that one does:
     * denied statement by statement, and not the denial of a disjunction of them.
     */
    @Test
    void aConditionInTheBodyIsWhatItStatesOnTheApplicationARunMeetsItOn() {
        Proposition.OnAnApplication inside = assertInstanceOf(
                Proposition.OnAnApplication.class,
                theOneConditionIn("List.any(m -> m.days > 3, [w.first, w.second])"));
        assertEquals(List.of(stated("w.first.days > 3"), stated("w.second.days > 3")),
                inside.each());
        Proposition.OnAnApplication failing = assertInstanceOf(
                Proposition.OnAnApplication.class, inside.denied());
        assertEquals(List.of(stated("w.first.days <= 3"), stated("w.second.days <= 3")),
                failing.each());
    }

    @Test
    void oneStatementOnEveryApplicationIsThatStatement() {
        Proposition one = stated("w.n > 1");
        assertEquals(one, Proposition.onAnApplication(List.of(one, one)));
        Proposition other = stated("w.n > 2");
        assertEquals(Proposition.onAnApplication(List.of(one, other)),
                Proposition.onAnApplication(List.of(other, one)),
                "which application was read first says nothing");
    }

    /** What the condition of {@code f}'s one fork states, its fork written as {@code condition}. */
    private static Proposition stated(String condition) {
        Model model = model(condition);
        Core.If fork = assertInstanceOf(Core.If.class, Core.withoutStanding(model.analysis.core()),
                "the body is the fork");
        return Pullback.ofATruth(fork.cond(), model.reads, model.inputs.reading(model.rules),
                Optional.empty()).proposition();
    }

    /** What the one comparison inside the fork's condition states, as the body's meanings file
     *  it. */
    private static Proposition theOneConditionIn(String condition) {
        Model model = model(condition);
        MeaningsOfABody meanings = MeaningsOfABodyReading.of(model.analysis,
                () -> model.inputs.reading(model.rules), model.reads, model.rules.symbols(),
                model.rules.newtypes());
        List<Proposition> inside = meanings.stated().entrySet().stream()
                .filter(each -> each.getKey().part() == MeaningsOfABody.Part.ITSELF)
                .map(each -> each.getValue().states())
                .toList();
        assertEquals(1, inside.size(), () -> "one comparison is written: " + inside);
        return inside.getFirst();
    }

    private record Model(AnalysisBody analysis, InputDomain inputs, RuleReadingSource rules,
                         InputReads reads) {}

    private static Model model(String condition) {
        String source = "module demo\n\n" + INPUT + """

                behavior f : (w: Window) -> Int
                let f (w) = if %s then 1 else 0
                """.formatted(condition);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), () -> "the model compiles: " + condition);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        assertNotNull(checked, "the model under test compiles");
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("f");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        return new Model(analysis, inputs, rules, reads);
    }
}
