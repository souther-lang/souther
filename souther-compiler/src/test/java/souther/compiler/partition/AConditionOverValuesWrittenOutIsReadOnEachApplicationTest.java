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
import souther.compiler.meaning.WhyUnread;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

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

    /**
     * An application an operation stops before is still among the statements: {@code List.any}
     * stops at the first element that holds, so the second is never handed to it. What the
     * statements say can come out includes everything a run gives, which is all they are read for.
     */
    @Test
    void anApplicationNoRunMakesIsAStatementTooManyAndNeverOneTooFew() {
        Proposition inside = theOneConditionIn("List.any(m -> m.days == 1, [w.first, w.second])");
        assertInstanceOf(Proposition.OnAnApplication.class, inside);
        assertTrue(TruthOutcomes.of(inside).allows(true) && TruthOutcomes.of(inside).allows(false),
                "either way, since either element may be the one a run is on");
        Proposition settled = theOneConditionIn("List.any(x -> x == 1, [1, 2])");
        assertTrue(TruthOutcomes.of(settled).allows(true),
                () -> "the run holds on its first application and stops: " + settled);
        assertEquals(new Proposition.Always(true),
                stated("List.any(x -> x == 1, [1, 2])"), "what some element meets is exact");
    }

    /**
     * Past how many readings of one condition are made, a closure's applications are not read
     * one by one, and what is read in their place says that this compiler declined the work.
     */
    @Test
    void moreApplicationsThanAreReadAreDeclinedAndSaySo() {
        int most = CompositionBudget.READINGS_OF_ONE_CONDITION.maximum();
        assertInstanceOf(Proposition.Any.class,
                stated("List.any(x -> w.n == x, " + values(most) + ")"),
                "as many applications as are read are read one by one");
        Proposition.Unread past = assertInstanceOf(Proposition.Unread.class,
                stated("List.any(x -> w.n == x, " + values(most + 1) + ")"));
        assertEquals(new WhyUnread.MoreReadingsThanAreMade(), past.why());
        Proposition.Unread inside = assertInstanceOf(Proposition.Unread.class,
                theOneConditionIn("List.any(x -> w.n == x, " + values(most + 1) + ")"));
        assertEquals(new WhyUnread.MoreReadingsThanAreMade(), inside.why(),
                "and a condition in the body is filed as declined, not read on fewer of them");
    }

    /** What multiplies is the nesting, and it is counted down the tree, outer applications and
     *  all. */
    @Test
    void nestedApplicationsAreCountedTogether() {
        int side = (int) Math.sqrt(CompositionBudget.READINGS_OF_ONE_CONDITION.maximum());
        String within = "List.any(x -> List.any(y -> w.n == x + y, " + values(side) + "), "
                + values(side) + ")";
        assertFalse(unreadIn(stated(within)), () -> "within the figure: " + stated(within));
        String past = "List.any(x -> List.any(y -> w.n == x + y, " + values(side + 1) + "), "
                + values(side + 1) + ")";
        assertTrue(unreadIn(stated(past)), "each closure alone is within the figure, and the"
                + " two together are past it");
    }

    /** The cases of each side of a comparison are compared with each other's, and counted so. */
    @Test
    void casesComparedWithCasesAreCountedTogether() {
        int side = (int) Math.sqrt(CompositionBudget.READINGS_OF_ONE_CONDITION.maximum());
        Proposition within = stated(choices("w.n", side) + " > " + choices("w.first.days", side));
        assertFalse(unreadIn(within), () -> "within the figure: " + within);
        Proposition past = stated(choices("w.n", side + 1) + " > "
                + choices("w.first.days", side + 1));
        assertEquals(List.of(new WhyUnread.MoreReadingsThanAreMade()), whysIn(past));
    }

    /** {@code [0, 1, ..., count - 1]}. */
    private static String values(int count) {
        return IntStream.range(0, count).mapToObj(String::valueOf)
                .collect(Collectors.joining(", ", "[", "]"));
    }

    /** A value chosen by {@code count} cases of {@code subject}. */
    private static String choices(String subject, int count) {
        StringBuilder out = new StringBuilder("(");
        for (int at = 1; at < count; at++) {
            out.append("if ").append(subject).append(" == ").append(at).append(" then ")
                    .append(at).append(" else ");
        }
        return out.append("0)").toString();
    }

    private static boolean unreadIn(Proposition stated) {
        return !whysIn(stated).isEmpty();
    }

    private static List<WhyUnread> whysIn(Proposition stated) {
        return switch (stated) {
            case Proposition.Unread unread -> List.of(unread.why());
            case Proposition.All all -> all.parts().stream().flatMap(p -> whysIn(p).stream())
                    .toList();
            case Proposition.Any any -> any.parts().stream().flatMap(p -> whysIn(p).stream())
                    .toList();
            case Proposition.OnAnApplication on -> on.each().stream()
                    .flatMap(p -> whysIn(p).stream()).toList();
            case Proposition.Some some -> whysIn(some.ofTheElement());
            default -> List.of();
        };
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
