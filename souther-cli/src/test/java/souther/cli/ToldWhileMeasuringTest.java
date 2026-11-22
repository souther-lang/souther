package souther.cli;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Answer;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.query.Key;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a run says on the error stream while it measures: nothing while the wait is short, what it
 * measures once it is not, and at each minute which behavior it is on.
 *
 * <p>The time is handed in here ({@link ToldWhileMeasuring#after}), so what is said at a second
 * is asked at that second and no test waits for one.
 */
class ToldWhileMeasuringTest {

    private static final String MODEL = """
            module told.model

            behavior once : (n: Int) -> Int
            let once (n) = n

            behavior twice : (n: Int) -> Int
            let twice (n) = n + n

            example once
                | "one" : (1) -> 1

            example twice
                | "two" : (1) -> 2
            """;

    private final ByteArrayOutputStream written = new ByteArrayOutputStream();
    private final PrintStream err = new PrintStream(written, true, StandardCharsets.UTF_8);

    private List<String> said() {
        String text = written.toString(StandardCharsets.UTF_8);
        return text.isEmpty() ? List.of() : text.lines().toList();
    }

    private static Compilation measured(String behavior) {
        Compilation compilation = Compilation.ofSource(MODEL, "told.model");
        compilation.choose(new Adequacy.Choice(null, behavior));
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return compilation;
    }

    @Test
    void aShortRunSaysNothingAndALongerOneSaysOnceWhatItMeasures() {
        try (ToldWhileMeasuring told = new ToldWhileMeasuring(err, Locale.ENGLISH)) {
            told.listenTo(measured(null));

            told.after(ToldWhileMeasuring.SAYS_WHAT_IT_MEASURES_AFTER_SECONDS - 1);
            assertEquals(List.of(), said());

            told.after(ToldWhileMeasuring.SAYS_WHAT_IT_MEASURES_AFTER_SECONDS);
            told.after(ToldWhileMeasuring.SAYS_WHAT_IT_MEASURES_AFTER_SECONDS + 1);
            told.after(ToldWhileMeasuring.SAYS_WHERE_IT_IS_EVERY_SECONDS - 1);
            assertEquals(List.of("measuring `told.model` (2 behaviors)"), said());
        }
    }

    @Test
    void theOneBehaviorARunWasNarrowedToIsNamed() {
        try (ToldWhileMeasuring told = new ToldWhileMeasuring(err, Locale.ENGLISH)) {
            told.listenTo(measured("twice"));

            told.after(ToldWhileMeasuring.SAYS_WHAT_IT_MEASURES_AFTER_SECONDS);

            assertEquals(List.of("measuring `told.model.twice`"), said());
        }
    }

    /** A question about one behavior, which says how long the run has taken while it is being
     *  worked out. */
    private record WorkedOutAt(String name, String behavior, long seconds) implements Key<Long> {

        static ToldWhileMeasuring told;

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Long> compute(Db db) {
            told.after(seconds);
            return Answer.of(seconds);
        }
    }

    /** A question about one behavior that is answered by asking {@code asks}. */
    private record Asking(String name, String behavior, WorkedOutAt asks) implements Key<Long> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Long> compute(Db db) {
            return db.ask(asks);
        }
    }

    @Test
    void whereABehaviorIsReadForAnotherItSaysBoth() {
        try (ToldWhileMeasuring told = new ToldWhileMeasuring(err, Locale.ENGLISH)) {
            Compilation compilation = measured("once");
            told.listenTo(compilation);
            WorkedOutAt.told = told;

            compilation.db().ask(new Asking("told.model", "once",
                    new WorkedOutAt("told.model", "twice", 60)));

            assertEquals(List.of(
                    "measuring `told.model.once`",
                    "1 min so far; now measuring `told.model.once`, and reading"
                            + " `told.model.twice` for it"), said());
        }
    }

    @Test
    void eachMinuteItSaysOnceWhichBehaviorItIsOn() {
        try (ToldWhileMeasuring told = new ToldWhileMeasuring(err, Locale.ENGLISH)) {
            Compilation compilation = measured(null);
            told.listenTo(compilation);
            WorkedOutAt.told = told;
            told.after(ToldWhileMeasuring.SAYS_WHAT_IT_MEASURES_AFTER_SECONDS);

            compilation.db().ask(new WorkedOutAt("told.model", "once", 60));
            compilation.db().ask(new WorkedOutAt("told.model", "once", 61));
            compilation.db().ask(new WorkedOutAt("told.model", "twice", 125));
            told.after(180);

            assertEquals(List.of(
                    "measuring `told.model` (2 behaviors)",
                    "1 min so far; now measuring `told.model.once`",
                    "2 min so far; now measuring `told.model.twice`",
                    "3 min so far; still measuring"), said());
        }
    }

    @Test
    void itSaysItInTheLanguageTheRunWasAskedFor() {
        try (ToldWhileMeasuring told = new ToldWhileMeasuring(err, Locale.JAPANESE)) {
            Compilation compilation = measured(null);
            told.listenTo(compilation);
            WorkedOutAt.told = told;

            told.after(ToldWhileMeasuring.SAYS_WHAT_IT_MEASURES_AFTER_SECONDS);
            compilation.db().ask(new WorkedOutAt("told.model", "once", 60));

            assertEquals(List.of(
                    "`told.model`（behavior 2 個） を測っています",
                    "1 分たちました。いま測っているのは `told.model.once` です"), said());
        }
    }
}
