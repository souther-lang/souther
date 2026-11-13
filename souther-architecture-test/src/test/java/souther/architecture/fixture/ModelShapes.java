package souther.architecture.fixture;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.time.LocalDate;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Supplier;

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

        public static Compilation notCompiled(Compilation model, String reason) {
            Objects.requireNonNull(reason);
            return model;
        }
    }

    /** Makes models in a class of its own, as a test that shares what it builds does. */
    public static final class Factory {

        private Factory() { }

        public static Compilation made(String source) {
            return Compilation.ofSource(source, "Main");
        }

        public static Compilation asked(String source) {
            return TheDoor.answered(source);
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

    /** Gives the variable the asked model on one way only, so the other reads the one it had. */
    public static final class ReassignedOnOneWay {

        private ReassignedOnOneWay() { }

        public static AdequacyReport read(String source, boolean careful) {
            Compilation model = Compilation.ofSource(source, "Main");
            if (careful) {
                model = TheDoor.compiles(model);
            }
            return AdequacyReport.of(model);
        }
    }

    /** Asks about the model on each of the ways, and gives the variable the answer on each. */
    public static final class AskedOnEveryWay {

        private AskedOnEveryWay() { }

        public static AdequacyReport read(String source, boolean careful) {
            Compilation model = Compilation.ofSource(source, "Main");
            if (careful) {
                model = TheDoor.compiles(model);
            } else {
                model = TheDoor.refusedWith(List.of(), model);
            }
            return AdequacyReport.of(model);
        }
    }

    /** Keeps the model in a field, written where it is made and never asked about. */
    public static final class FieldNeverAsked {

        private Compilation model;

        public AdequacyReport read(String source) {
            model = Compilation.ofSource(source, "Main");
            return AdequacyReport.of(model);
        }
    }

    /** Keeps the model in a field, written only as what was asked about. */
    public static final class FieldAskedWhereWritten {

        private Compilation model;

        public AdequacyReport read(String source) {
            model = TheDoor.answered(source);
            return AdequacyReport.of(model);
        }
    }

    /** Takes a model made in a class of its own, which nobody asked about. */
    public static final class AnotherClassMadeIt {

        private AnotherClassMadeIt() { }

        public static AdequacyReport read(String source) {
            Compilation model = Factory.made(source);
            return AdequacyReport.of(model);
        }
    }

    /** Takes a model made in a class of its own, which asked about it. */
    public static final class AnotherClassAskedAboutIt {

        private AnotherClassAskedAboutIt() { }

        public static AdequacyReport read(String source) {
            Compilation model = Factory.asked(source);
            return AdequacyReport.of(model);
        }
    }

    /** A model that is handed on through more methods than there are rounds to follow it. */
    public static final class HandedOnManyTimes {

        private HandedOnManyTimes() { }

        private static Compilation a0(String source) {
            return Compilation.ofSource(source, "Main");
        }

        private static Compilation a1(String source) {
            return a0(source);
        }

        private static Compilation a2(String source) {
            return a1(source);
        }

        private static Compilation a3(String source) {
            return a2(source);
        }

        private static Compilation a4(String source) {
            return a3(source);
        }

        private static Compilation a5(String source) {
            return a4(source);
        }

        private static Compilation a6(String source) {
            return a5(source);
        }

        private static Compilation a7(String source) {
            return a6(source);
        }

        private static Compilation a8(String source) {
            return a7(source);
        }

        private static Compilation a9(String source) {
            return a8(source);
        }

        private static Compilation a10(String source) {
            return a9(source);
        }

        private static Compilation a11(String source) {
            return a10(source);
        }

        private static Compilation a12(String source) {
            return a11(source);
        }

        private static Compilation a13(String source) {
            return a12(source);
        }

        public static AdequacyReport read(String source) {
            return AdequacyReport.of(a13(source));
        }
    }

    /** Asks about the model, and drops what the failure of that said. */
    public static final class SwallowedFailure {

        private SwallowedFailure() { }

        public static AdequacyReport read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            try {
                TheDoor.compiles(model);
            } catch (AssertionError failed) {
                Objects.requireNonNull(failed);
            }
            return AdequacyReport.of(model);
        }
    }

    /** Makes the model inside a lambda and reads it there. */
    public static final class MadeInALambda {

        private MadeInALambda() { }

        public static Supplier<AdequacyReport> read(String source) {
            return () -> AdequacyReport.of(Compilation.ofSource(source, "Main"));
        }
    }

    /** Hands a model that was asked about to a lambda, which reads it. */
    public static final class AskedThenCaptured {

        private AskedThenCaptured() { }

        public static Supplier<AdequacyReport> read(String source) {
            Compilation model = TheDoor.answered(source);
            return () -> AdequacyReport.of(model);
        }
    }

    /** Takes a model out of a collection, where nothing says what was done with it. */
    public static final class FromACollection {

        private FromACollection() { }

        public static AdequacyReport read(Map<String, Compilation> models) {
            return AdequacyReport.of(models.get("a"));
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

    /** Reads the report of a model a caller hands in, having asked about it. */
    public static final class ParameterHandedByACaller {

        private ParameterHandedByACaller() { }

        private static AdequacyReport reportOf(Compilation model) {
            return AdequacyReport.of(model);
        }

        public static AdequacyReport read(String source) {
            return reportOf(TheDoor.answered(source));
        }
    }

    /** Reads the report of a model nobody hands it, as a method the test engine runs does. */
    public static final class ParameterNobodyPasses {

        private ParameterNobodyPasses() { }

        public static AdequacyReport read(Compilation model) {
            return AdequacyReport.of(model);
        }
    }

    /** Makes a lambda that would ask about the model, and never runs it. */
    public static final class LambdaMadeNotRun {

        private LambdaMadeNotRun() { }

        public static AdequacyReport read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            Runnable later = () -> TheDoor.compiles(model);
            Objects.requireNonNull(later);
            return AdequacyReport.of(model);
        }
    }

    /** Hands an asked-about model new sources and reads it. */
    public static final class UpdatedAfterTheLook {

        private UpdatedAfterTheLook() { }

        public static AdequacyReport read(String source, Map<String, String> other) {
            Compilation model = TheDoor.answered(source);
            model.update(other, Set.of(), LocalDate.MIN);
            return AdequacyReport.of(model);
        }
    }

    /** Hands an asked-about model a day and reads it. */
    public static final class MutatedAfterTheLook {

        private MutatedAfterTheLook() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            model.writtenOn(LocalDate.MIN);
            return AdequacyReport.of(model);
        }
    }

    /** Hands a model new sources, and asks about it as it then is. */
    public static final class UpdatedThenAsked {

        private UpdatedThenAsked() { }

        public static AdequacyReport read(String source, Map<String, String> other) {
            Compilation model = TheDoor.answered(source);
            model.update(other, Set.of(), LocalDate.MIN);
            TheDoor.compiles(model);
            return AdequacyReport.of(model);
        }
    }

    /** Reads the model through a second variable it was copied to, having asked through the first. */
    public static final class AliasOfAnAskedModel {

        private AliasOfAnAskedModel() { }

        public static AdequacyReport read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            Compilation alias = model;
            TheDoor.compiles(model);
            return AdequacyReport.of(alias);
        }
    }

    /** Reads what the model says of its warnings without having asked about it. */
    public static final class WarningsOfAnUnaskedModel {

        private WarningsOfAnUnaskedModel() { }

        public static boolean read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            return model.warnings().isEmpty();
        }
    }

    /** Says a model is read without compiling it, in a method that is not on the list. */
    public static final class NotCompiledOffTheList {

        private NotCompiledOffTheList() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.notCompiled(Compilation.ofSource(source, "Main"), "no");
            return AdequacyReport.of(model);
        }
    }

    /** Says a model is read without compiling it, in a method that is on the list. */
    public static final class NotCompiledOnTheList {

        private NotCompiledOnTheList() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.notCompiled(Compilation.ofSource(source, "Main"), "too long");
            return AdequacyReport.of(model);
        }
    }
}
