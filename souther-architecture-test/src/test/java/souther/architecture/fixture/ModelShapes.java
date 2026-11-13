package souther.architecture.fixture;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The shapes a test reads the report of a model in, written to be read by the check that refuses
 * some of them. None of these is run.
 */
public final class ModelShapes {

    private ModelShapes() { }

    /** The model of a test, answered by nothing but this class's own look. */
    public static final class TheStopOnAnError {

        private TheStopOnAnError() { }

        public static Compilation compiles(Compilation model) {
            assertEquals(List.of(), model.errors());
            return model;
        }
    }

    /** Compiles, measures and reads, and never asks whether the model compiled. */
    public static final class LeftOpenFor {

        private LeftOpenFor() { }

        public static AdequacyReport read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            model.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
            model.answerEverything();
            return AdequacyReport.of(model);
        }
    }

    /** Makes the model in one method and reads it in another, so no one method has both. */
    public static final class MeasuredThenRead {

        private MeasuredThenRead() { }

        static Compilation measured(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            model.answerEverything();
            return model;
        }

        static AdequacyReport unmetOf(Compilation model) {
            return AdequacyReport.of(model);
        }

        public static AdequacyReport read(String source) {
            return unmetOf(measured(source));
        }
    }

    /** Looks at the errors and does nothing with what it saw. */
    public static final class ErrorsDropped {

        private ErrorsDropped() { }

        public static AdequacyReport read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            model.answerEverything();
            model.errors();
            return AdequacyReport.of(model);
        }
    }

    /** Asks the model compiles through the door that stops on an error. */
    public static final class ThroughTheDoor {

        private ThroughTheDoor() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheStopOnAnError.compiles(Compilation.ofSource(source, "Main"));
            return AdequacyReport.of(model);
        }
    }

    /** Asks the model compiles by comparing its errors, as a test of a model that does not does. */
    public static final class TheErrorsAreWhatWasMeant {

        private TheErrorsAreWhatWasMeant() { }

        public static AdequacyReport read(String source, int expected) {
            Compilation model = Compilation.ofSource(source, "Main");
            model.answerEverything();
            assertEquals(expected, model.errors().size());
            return AdequacyReport.of(model);
        }
    }

    /** A model with nothing to report, whose emptiness is the answer, asked about first. */
    public static final class AnEmptyReportThatIsTheAnswer {

        private AnEmptyReportThatIsTheAnswer() { }

        public static boolean read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            model.answerEverything();
            assertEquals(List.of(), model.errors());
            return AdequacyReport.of(model).modules().isEmpty();
        }
    }
}
