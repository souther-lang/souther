package souther.architecture.fixture;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.time.LocalDate;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The shapes a test reads the report of a model in, written to be read by the check that refuses
 * some of them. None of these is run.
 */
public final class ModelShapes {

    private ModelShapes() { }

    /** The model of a test, asked about by nothing but this class's own look. */
    public static final class TheDoor {

        private TheDoor() { }

        public static Compilation answered(String source) {
            return compiles(Compilation.ofSource(source, "Main"));
        }

        public static Compilation compiles(Compilation model) {
            return refusedWith(List.of(), model);
        }

        public static Compilation refusedWith(List<String> codes, Compilation model) {
            model.answerEverything();
            assertEquals(codes, model.errors());
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

    /** Keeps what the errors showed and asserts nothing of it. */
    public static final class ErrorsKept {

        private ErrorsKept() { }

        public static AdequacyReport read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            model.answerEverything();
            boolean none = model.errors().isEmpty();
            return none ? AdequacyReport.of(model) : null;
        }
    }

    /** Makes the model and has it answer for itself with a day, and reads that one. */
    public static final class ADerivedModelNeverAsked {

        private ADerivedModelNeverAsked() { }

        public static AdequacyReport read(String source) {
            Compilation model = Compilation.ofSource(source, "Main").writtenOn(LocalDate.MIN);
            return AdequacyReport.of(model);
        }
    }

    /** The same, asked about once it is the one in hand. */
    public static final class ADerivedModelAsked {

        private ADerivedModelAsked() { }

        public static AdequacyReport read(String source) {
            Compilation model = Compilation.ofSource(source, "Main").writtenOn(LocalDate.MIN);
            TheDoor.compiles(model);
            return AdequacyReport.of(model);
        }
    }

    /** Reads what the model has computed before anything is answered, and asks at the end. */
    public static final class AskedAfterTheRead {

        private AskedAfterTheRead() { }

        public static AdequacyReport read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            AdequacyReport report = AdequacyReport.of(model);
            TheDoor.compiles(model);
            return report;
        }
    }

    /** Reads the report and may leave before the ask that comes after it. */
    public static final class LeftBeforeTheAsk {

        private LeftBeforeTheAsk() { }

        public static AdequacyReport read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            AdequacyReport report = AdequacyReport.of(model);
            if (report == null) {
                return null;
            }
            TheDoor.compiles(model);
            return report;
        }
    }

    /** Asks about one model and reads the report of another. */
    public static final class AnotherModelAsked {

        private AnotherModelAsked() { }

        public static AdequacyReport read(String source, String other) {
            Compilation asked = Compilation.ofSource(source, "Main");
            Compilation read = Compilation.ofSource(other, "Main");
            TheDoor.compiles(asked);
            return AdequacyReport.of(read);
        }
    }

    /** Asks about a model and then reads the report of the one that took its place. */
    public static final class ReplacedAfterTheLook {

        private ReplacedAfterTheLook() { }

        public static AdequacyReport read(String source, String other) {
            Compilation model = Compilation.ofSource(source, "Main");
            TheDoor.compiles(model);
            model = Compilation.ofSource(other, "Main");
            return AdequacyReport.of(model);
        }
    }

    /** Asks about the model on one way to the read and not on the other. */
    public static final class AskedOnOneWayOnly {

        private AskedOnOneWayOnly() { }

        public static AdequacyReport read(String source, boolean careful) {
            Compilation model = Compilation.ofSource(source, "Main");
            if (careful) {
                TheDoor.compiles(model);
            }
            return AdequacyReport.of(model);
        }
    }

    /** Asks the model compiles through the door that stops on an error. */
    public static final class ThroughTheDoor {

        private ThroughTheDoor() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.compiles(Compilation.ofSource(source, "Main"));
            return AdequacyReport.of(model);
        }
    }

    /** Asks about the model by name, after making it, and then reads it. */
    public static final class AskedThenRead {

        private AskedThenRead() { }

        public static AdequacyReport read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            model.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
            TheDoor.compiles(model);
            return AdequacyReport.of(model);
        }
    }

    /** Says what the errors of the model are meant to be, as a test of a model that does not compile. */
    public static final class TheErrorsAreWhatWasMeant {

        private TheErrorsAreWhatWasMeant() { }

        public static AdequacyReport read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            TheDoor.refusedWith(List.of("E1013"), model);
            return AdequacyReport.of(model);
        }
    }

    /** Asks in a method of its own, and reads what it was handed in another. */
    public static final class AskedByAMethodOfItsOwn {

        private AskedByAMethodOfItsOwn() { }

        private static void check(Compilation model) {
            TheDoor.compiles(model);
        }

        private static AdequacyReport reportOf(Compilation model) {
            return AdequacyReport.of(model);
        }

        public static AdequacyReport read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            check(model);
            return reportOf(model);
        }
    }

    /** Reads the report of a model that was handed in, which was asked about where it was made. */
    public static final class HandedIn {

        private HandedIn() { }

        public static AdequacyReport read(Compilation model) {
            return AdequacyReport.of(model);
        }
    }
}
