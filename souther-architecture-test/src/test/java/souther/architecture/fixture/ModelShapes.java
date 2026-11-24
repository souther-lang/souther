package souther.architecture.fixture;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.RepeatedTest;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Answer;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.report.AdequacyReport;
import souther.compiler.source.SourceId;

import java.time.LocalDate;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Stream;

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

        public static List<String> diagnosticsOf(Compilation model) {
            model.answerEverything();
            return List.of();
        }

        public static Compilation passedThrough(Compilation model) {
            return model;
        }
    }

    /** Takes a model back from a call of the helper that checks nothing, and reads its report. */
    public static final class HandedBackByACallThatChecksNothing {

        private HandedBackByACallThatChecksNothing() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.passedThrough(Compilation.ofSource(source, "Main"));
            return AdequacyReport.of(model);
        }
    }

    /** Answers the warnings of a module, which is not answering everything, and reads the errors. */
    public static final class AnswerWarningsOnly {

        private AnswerWarningsOnly() { }

        public static boolean read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            model.answerWarnings("Main");
            return model.errors().isEmpty();
        }
    }

    /** Takes what the errors of a model are, which does not say the model compiles, and reads. */
    public static final class DiagnosticsAreNotACompileCheck {

        private DiagnosticsAreNotACompileCheck() { }

        public static AdequacyReport read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            TheDoor.diagnosticsOf(model);
            return AdequacyReport.of(model);
        }
    }

    /** Answers a model in full and reads all it found, which holds the warnings among the errors. */
    public static final class ReportsOfAnAnsweredModel {

        private ReportsOfAnAnsweredModel() { }

        public static boolean read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            model.answerEverything();
            return model.reports().isEmpty();
        }
    }

    /** Answers a model in full and reads the diagnostics, which say what was found of it. */
    public static final class DiagnosticsOfAModelNobodyAsked {

        private DiagnosticsOfAModelNobodyAsked() { }

        public static boolean read(String source) {
            return Compilation.ofSource(source, "Main").diagnostics().isEmpty();
        }
    }

    /** Answers a model in full and reads its errors, which a model that did not compile shows. */
    public static final class ErrorsOfAnAnsweredModel {

        private ErrorsOfAnAnsweredModel() { }

        public static boolean read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            model.answerEverything();
            return model.errors().isEmpty();
        }
    }

    /** Hands a model to a function that is known by what it takes in general, which changes it. */
    public static final class ChangedThroughAGenericFunction {

        private ChangedThroughAGenericFunction() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            Consumer<Compilation> updater =
                    each -> each.update(Map.of(), Set.of(), LocalDate.MIN);
            updater.accept(model);
            return AdequacyReport.of(model);
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

    /** Says a model is read without compiling it, and reads what its declarations say. */
    public static final class NotCompiledOnTheList {

        private NotCompiledOnTheList() { }

        public static boolean read(String source) {
            Compilation model = TheDoor.notCompiled(Compilation.ofSource(source, "Main"),
                    "too long");
            return model.db() != null;
        }
    }

    /** Says a model is read without compiling it, and then reads a report of it. */
    public static final class NotCompiledButReportRead {

        private NotCompiledButReportRead() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.notCompiled(Compilation.ofSource(source, "Main"),
                    "too long");
            return AdequacyReport.of(model);
        }
    }

    /** Reads the report first, changes the model, and asks about it as it then is. */
    public static final class ReadThenChangedThenAsked {

        private ReadThenChangedThenAsked() { }

        public static AdequacyReport read(String source, Map<String, String> other) {
            Compilation model = Compilation.ofSource(source, "Main");
            AdequacyReport report = AdequacyReport.of(model);
            model.update(other, Set.of(), LocalDate.MIN);
            TheDoor.compiles(model);
            return report;
        }
    }

    /** Asks about the model, and has a method of its own change it before the read. */
    public static final class ChangedThroughAMethod {

        private ChangedThroughAMethod() { }

        private static void changeSource(Compilation model, Map<String, String> sources) {
            model.update(sources, Set.of(), LocalDate.MIN);
        }

        public static AdequacyReport read(String source, Map<String, String> other) {
            Compilation model = TheDoor.answered(source);
            changeSource(model, other);
            return AdequacyReport.of(model);
        }
    }

    /** Asks about the model, and changes what it is compiled from through the store it hands out. */
    public static final class ChangedThroughTheDb {

        private ChangedThroughTheDb() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            model.db().forget(new SourceId("main.sou"), "main");
            return AdequacyReport.of(model);
        }
    }

    /** Reads what a model has found without anything having been answered. */
    public static final class ReportsReadOfAModelNobodyAsked {

        private ReportsReadOfAModelNobodyAsked() { }

        public static boolean read(String source) {
            return Compilation.ofSource(source, "Main").reports().isEmpty();
        }
    }

    /** What a model is handed to, by a name that more than one method answers to. */
    public interface Editor {

        void change(Compilation model);
    }

    /** An editor that replaces what the model is compiled from. */
    public static final class UpdatingEditor implements Editor {

        @Override
        public void change(Compilation model) {
            model.update(Map.of(), Set.of(), LocalDate.MIN);
        }
    }

    /** An editor that looks at the model and leaves it as it was. */
    public static final class LookingEditor implements Editor {

        @Override
        public void change(Compilation model) {
            Objects.requireNonNull(model.db());
        }
    }

    /** Hands an asked-about model to an editor that is only known by its interface. */
    public static final class ChangedThroughAnInterface {

        private ChangedThroughAnInterface() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            Editor editor = new UpdatingEditor();
            editor.change(model);
            return AdequacyReport.of(model);
        }
    }

    /** Hands an asked-about model to an editor that only looks at it. */
    public static final class HandedToAnInterfaceThatOnlyLooks {

        private HandedToAnInterfaceThatOnlyLooks() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            LookingEditor editor = new LookingEditor();
            editor.change(model);
            return AdequacyReport.of(model);
        }
    }

    /** Asks about a model on the way it returns, and changes it on the way it fails. */
    public static final class ChangedOnTheWayThatFails {

        private ChangedOnTheWayThatFails() { }

        private static void changeOrCheck(Compilation model, boolean fail) {
            if (fail) {
                model.update(Map.of(), Set.of(), LocalDate.MIN);
                throw new IllegalStateException("failed");
            }
            TheDoor.compiles(model);
        }

        public static AdequacyReport read(String source, boolean fail) {
            Compilation model = TheDoor.answered(source);
            try {
                changeOrCheck(model, fail);
            } catch (IllegalStateException failed) {
                return AdequacyReport.of(model);
            }
            return null;
        }
    }

    /** Keeps an asked-about model in a field, and changes it by the variable it came in. */
    public static final class FieldChangedByTheVariableItCameIn {

        private Compilation stored;

        public AdequacyReport read(String source, Map<String, String> other) {
            Compilation model = TheDoor.answered(source);
            stored = model;
            model.update(other, Set.of(), LocalDate.MIN);
            return AdequacyReport.of(stored);
        }
    }

    /** Reads a model out of a field into a variable, and changes it there. */
    public static final class FieldChangedByTheVariableItWasReadInto {

        private Compilation stored = TheDoor.answered("module a");

        public AdequacyReport read(Map<String, String> other) {
            Compilation model = stored;
            model.update(other, Set.of(), LocalDate.MIN);
            return AdequacyReport.of(stored);
        }
    }

    /** Reads a model that is the asked-about one on one way and nobody's on the other. */
    public static final class ConditionalModelJoin {

        private ConditionalModelJoin() { }

        public static boolean read(String source, boolean sound) {
            Compilation selected = sound ? TheDoor.answered(source)
                    : Compilation.ofSource(source, "Main");
            return selected.reports().isEmpty();
        }
    }

    /** Something that holds a model, of which there are as many as it is made. */
    public static final class Box {

        public Compilation model;
    }

    /** Writes an asked-about model to the field of one box and reads the field of another. */
    public static final class TwoBoxesOneFieldName {

        private TwoBoxesOneFieldName() { }

        public static boolean read(String source) {
            Box unsafe = new Box();
            Box safe = new Box();
            unsafe.model = Compilation.ofSource(source, "Main");
            safe.model = TheDoor.answered(source);
            return unsafe.model.reports().isEmpty();
        }
    }

    /** Hands the store of an asked-about model, kept in a variable, to a function that changes it. */
    public static final class DbHeldHandedToAConsumer {

        private DbHeldHandedToAConsumer() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            Db store = model.db();
            Consumer<Db> changer = db -> db.forget(new SourceId("main.sou"), "main");
            changer.accept(store);
            return AdequacyReport.of(model);
        }
    }

    /** Keeps what a question put to the store of a model that was answered is told in a variable. */
    public static final class AnswerKeptInAVariable {

        private AnswerKeptInAVariable() { }

        public static boolean read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            model.answerEverything();
            var answer = model.db().ask(new Adequacy.Witnesses("Main"));
            return answer.reports().isEmpty();
        }
    }

    /** Reads what a store says in a method that is handed the store of a model that was answered. */
    public static final class ReportsOfAStoreHandedIn {

        private ReportsOfAStoreHandedIn() { }

        private static boolean hasNoReports(Db store) {
            return store.ask(new Adequacy.Witnesses("Main")).reports().isEmpty();
        }

        public static boolean read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            model.answerEverything();
            return hasNoReports(model.db());
        }
    }

    /** The same, of the store of a model that was asked about. */
    public static final class ReportsOfAStoreHandedInAfterTheLook {

        private ReportsOfAStoreHandedInAfterTheLook() { }

        private static boolean hasNoReports(Db store) {
            return store.ask(new Adequacy.Witnesses("Main")).reports().isEmpty();
        }

        public static boolean read(String source) {
            Compilation model = TheDoor.answered(source);
            return hasNoReports(model.db());
        }
    }

    /** Reads the report of a model and asks that it compiles after, where the failure is dropped. */
    public static final class AskedAfterTheReadInATryThatDropsTheFailure {

        private AskedAfterTheReadInATryThatDropsTheFailure() { }

        public static AdequacyReport read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            AdequacyReport report = AdequacyReport.of(model);
            try {
                TheDoor.compiles(model);
            } catch (AssertionError dropped) {
                return report;
            }
            return report;
        }
    }

    /** Code of the compiler that reads the reports of the model it is handed. */
    public static final class ProductionReader {

        private ProductionReader() { }

        public static boolean hasNoReports(Compilation model) {
            return model.reports().isEmpty();
        }
    }

    /** Hands a model nobody asked about to code that reads its reports. */
    public static final class ReadByAProductionHelper {

        private ReadByAProductionHelper() { }

        public static boolean read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            return ProductionReader.hasNoReports(model);
        }
    }

    /** Hands a model that was asked about to code that reads its reports. */
    public static final class ReadByAProductionHelperAfterTheLook {

        private ReadByAProductionHelperAfterTheLook() { }

        public static boolean read(String source) {
            Compilation model = TheDoor.answered(source);
            return ProductionReader.hasNoReports(model);
        }
    }

    /** Reads the reports of an answer that a method handed back. */
    public static final class AnswerReturnedThroughAMethod {

        private AnswerReturnedThroughAMethod() { }

        private static <T> Answer<T> keep(Answer<T> answer) {
            return answer;
        }

        public static boolean read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            model.answerEverything();
            Answer<?> answer = keep(model.db().ask(new Adequacy.Witnesses("Main")));
            return answer.reports().isEmpty();
        }
    }

    /** Reads what an answered model's store answers to a question, which is empty if it stopped. */
    public static final class ValueOfAnAnswerOfAnAnsweredModel {

        private ValueOfAnAnswerOfAnAnsweredModel() { }

        public static boolean read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            model.answerEverything();
            return model.db().ask(new Adequacy.Witnesses("Main")).value() == null;
        }
    }

    /** Reads what the store of a model that was asked about answers to a question. */
    public static final class ValueOfAnAnswerOfACheckedModel {

        private ValueOfAnAnswerOfACheckedModel() { }

        public static boolean read(String source) {
            Compilation model = TheDoor.answered(source);
            return model.db().ask(new Adequacy.Witnesses("Main")).value() == null;
        }
    }

    /** Makes a store of its own and hands back the one it was given when it is told to. */
    public static final class ChoosesBetweenAStoreItMadeAndTheOneGiven {

        private ChoosesBetweenAStoreItMadeAndTheOneGiven() { }

        private static Db choose(Db existing, boolean useExisting) {
            Db fresh = new Db();
            return useExisting ? existing : fresh;
        }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            Db store = choose(model.db(), true);
            store.forget(new SourceId("main.sou"), "main");
            return AdequacyReport.of(model);
        }
    }

    /** Makes a store of its own on every way, and changes it. */
    public static final class ChangesAStoreItWasHandedThatIsNoModels {

        private ChangesAStoreItWasHandedThatIsNoModels() { }

        private static Db made() {
            return new Db();
        }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            Db own = made();
            own.forget(new SourceId("main.sou"), "main");
            return AdequacyReport.of(model);
        }
    }

    /** An interface whose method does nothing, which a class that has its own does not take. */
    public interface Silent {

        default void change(Compilation model) {
            Objects.requireNonNull(model);
        }
    }

    /** A class that changes the model it is handed. */
    public static class Parent {

        public void change(Compilation model) {
            model.update(Map.of(), Set.of(), LocalDate.MIN);
        }
    }

    /** Inherits the method of its class and has another of the same from its interface. */
    public static final class Child extends Parent implements Silent { }

    /** Changes an asked-about model by the method the class is run with, not the one of the interface. */
    public static final class ChangedThroughTheParentNotTheDefault {

        private ChangedThroughTheParentNotTheDefault() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            new Child().change(model);
            return AdequacyReport.of(model);
        }
    }

    /** Hands a copy of the variable that holds an asked-about model to a function that changes it. */
    public static final class CopyHandedToAConsumer {

        private CopyHandedToAConsumer() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            Compilation alias = model;
            Consumer<Compilation> updater = each -> each.update(Map.of(), Set.of(), LocalDate.MIN);
            updater.accept(alias);
            return AdequacyReport.of(model);
        }
    }

    /** Hands a variable that is given the asked-about model on some way to a function that changes it. */
    public static final class ReassignedCopyHandedToAConsumer {

        private ReassignedCopyHandedToAConsumer() { }

        public static AdequacyReport read(String source, boolean other) {
            Compilation model = TheDoor.answered(source);
            Compilation alias = TheDoor.answered("module b");
            if (other) {
                alias = model;
            }
            Consumer<Compilation> updater = each -> each.update(Map.of(), Set.of(), LocalDate.MIN);
            updater.accept(alias);
            return AdequacyReport.of(model);
        }
    }

    /** Changes an asked-about model by a variable that is given it on some way. */
    public static final class ReassignedCopyChangedDirectly {

        private ReassignedCopyChangedDirectly() { }

        public static AdequacyReport read(String source, boolean other) {
            Compilation model = TheDoor.answered(source);
            Compilation alias = TheDoor.answered("module b");
            if (other) {
                alias = model;
            }
            alias.update(Map.of(), Set.of(), LocalDate.MIN);
            return AdequacyReport.of(model);
        }
    }

    /** Makes the lambda that changes an asked-about model after the ask, and runs it. */
    public static final class LambdaMadeAfterTheAskAndRun {

        private LambdaMadeAfterTheAskAndRun() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            Runnable update = () -> model.update(Map.of(), Set.of(), LocalDate.MIN);
            update.run();
            return AdequacyReport.of(model);
        }
    }

    /** Reads the structural reports of a model nobody answered. */
    public static final class StructuralReportsOfAnUnasked {

        private StructuralReportsOfAnUnasked() { }

        public static boolean read(String source) {
            return Compilation.ofSource(source, "Main").structuralReports().isEmpty();
        }
    }

    /** Takes the structural failure of a model nobody answered. */
    public static final class StructuralFailureOfAnUnasked {

        private StructuralFailureOfAnUnasked() { }

        public static boolean read(String source) {
            return Compilation.ofSource(source, "Main").structuralFailure() == null;
        }
    }

    /** Reads every report of the store of a model that was answered, and not checked. */
    public static final class AllReportsOfAnAnswered {

        private AllReportsOfAnAnswered() { }

        public static boolean read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            model.answerEverything();
            return model.db().allReports().isEmpty();
        }
    }

    /** Asks the store of a model that was answered, and reads what the answer reports. */
    public static final class StoreAskOfAnAnswered {

        private StoreAskOfAnAnswered() { }

        public static boolean read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            model.answerEverything();
            return model.db().ask(new Adequacy.Witnesses("Main")).reports().isEmpty();
        }
    }

    /** Makes a lambda that changes a model before it is asked about, and runs it after. */
    public static final class LambdaCreatedBeforeTheAsk {

        private LambdaCreatedBeforeTheAsk() { }

        public static AdequacyReport read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            Runnable later = () -> model.update(Map.of(), Set.of(), LocalDate.MIN);
            TheDoor.compiles(model);
            later.run();
            return AdequacyReport.of(model);
        }
    }

    /** Changes a model through a method reference bound to it. */
    public static final class BoundMethodRefChanges {

        private BoundMethodRefChanges() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            Function<LocalDate, Compilation> derive = model::writtenOn;
            Objects.requireNonNull(derive.apply(LocalDate.MIN));
            return AdequacyReport.of(model);
        }
    }

    /** Reads the warnings of a model nobody asked about through a method reference bound to it. */
    public static final class BoundMethodRefReads {

        private BoundMethodRefReads() { }

        public static boolean read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            Supplier<List<?>> warned = model::warnings;
            return warned.get().isEmpty();
        }
    }

    /** Reads the warnings of a model nobody asked about through a method reference to the class. */
    public static final class UnboundMethodRefReads {

        private UnboundMethodRefReads() { }

        public static boolean read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            Function<Compilation, List<?>> warned = Compilation::warnings;
            return warned.apply(model).isEmpty();
        }
    }

    /** Reads the report of a model nobody asked about by mapping a container of it. */
    public static final class StaticMethodRefReads {

        private StaticMethodRefReads() { }

        public static boolean read(String source) {
            return Optional.of(Compilation.ofSource(source, "Main")).map(AdequacyReport::of)
                    .isEmpty();
        }
    }

    /** Hands a model that is in a field to a function that changes it. */
    public static final class FieldHandedToAConsumer {

        private Compilation model;

        public AdequacyReport read(String source) {
            model = TheDoor.answered(source);
            Consumer<Compilation> updater = each -> each.update(Map.of(), Set.of(), LocalDate.MIN);
            updater.accept(model);
            return AdequacyReport.of(model);
        }
    }

    /** Puts a model in an array that is handed to a function that changes what is in it. */
    public static final class BoxedInAnArray {

        private BoxedInAnArray() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            Object[] box = {model};
            Consumer<Object[]> updater = held -> ((Compilation) held[0])
                    .update(Map.of(), Set.of(), LocalDate.MIN);
            updater.accept(box);
            return AdequacyReport.of(model);
        }
    }

    /** Puts a model in an Optional and changes it by what runs on what is in it. */
    public static final class OptionalIfPresentChanges {

        private OptionalIfPresentChanges() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            Optional.ofNullable(model)
                    .ifPresent(each -> each.update(Map.of(), Set.of(), LocalDate.MIN));
            return AdequacyReport.of(model);
        }
    }

    /** Puts a model in a stream and changes it by what runs on each element. */
    public static final class StreamForEachChanges {

        private StreamForEachChanges() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            Stream.of(model).forEach(each -> each.update(Map.of(), Set.of(), LocalDate.MIN));
            return AdequacyReport.of(model);
        }
    }

    /** Keeps a model and changes it when it is told to, with nothing handed to it. */
    public static final class Holder {

        private final Compilation held;

        public Holder(Compilation held) {
            this.held = held;
        }

        public void change() {
            held.update(Map.of(), Set.of(), LocalDate.MIN);
        }
    }

    /** Hands an asked-about model to something that keeps it, and has it changed. */
    public static final class ChangedThroughAHolder {

        private ChangedThroughAHolder() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            Holder holder = new Holder(model);
            holder.change();
            return AdequacyReport.of(model);
        }
    }

    /** Something that is done, which is known by this name where it is run. */
    public interface Action {

        void act();
    }

    /** Changes an asked-about model from a class that is made on the spot. */
    public static final class ChangedThroughAnAnonymousClass {

        private ChangedThroughAnAnonymousClass() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            new Action() {
                @Override
                public void act() {
                    model.update(Map.of(), Set.of(), LocalDate.MIN);
                }
            }.act();
            return AdequacyReport.of(model);
        }
    }

    /** Changes the model of a field by a method that is handed nothing and gets it from a getter. */
    public static final class ChangedThroughAGetter {

        private Compilation model;

        private Compilation current() {
            return model;
        }

        private void change() {
            current().update(Map.of(), Set.of(), LocalDate.MIN);
        }

        public AdequacyReport read(String source) {
            model = TheDoor.answered(source);
            change();
            return AdequacyReport.of(model);
        }
    }

    /** Asks about a model it has a variable for, and has a method change the field it came from. */
    public static final class AskedAliasOfAFieldChangedByAMethod {

        private final Compilation stored = Compilation.ofSource("module a", "Main");

        private void change() {
            stored.update(Map.of(), Set.of(), LocalDate.MIN);
        }

        public AdequacyReport read() {
            Compilation model = stored;
            TheDoor.compiles(model);
            change();
            return AdequacyReport.of(model);
        }
    }

    /** Keeps the store of an asked-about model in a field, and has a method change it. */
    public static final class DbKeptInAFieldThenChanged {

        private Db store;

        private void reset() {
            store.forget(new SourceId("main.sou"), "main");
        }

        public AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            store = model.db();
            reset();
            return AdequacyReport.of(model);
        }
    }

    /** A class that changes the model it is handed. */
    public static class BaseChanger {

        public void rewrite(Compilation model) {
            model.update(Map.of(), Set.of(), LocalDate.MIN);
        }
    }

    /** A class that does not say how the model is changed, which it inherits. */
    public static final class SubChanger extends BaseChanger { }

    /** Changes an asked-about model by a method the class it names inherits. */
    public static final class ChangedThroughAnInheritedMethod {

        private ChangedThroughAnInheritedMethod() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            new SubChanger().rewrite(model);
            return AdequacyReport.of(model);
        }
    }

    /** An interface that changes the model it is handed, by a method it has a body for. */
    public interface DefaultChanger {

        default void rewrite(Compilation model) {
            model.update(Map.of(), Set.of(), LocalDate.MIN);
        }
    }

    /** A class that takes that method as it is. */
    public static final class DefaultImpl implements DefaultChanger { }

    /** Changes an asked-about model by a default method of an interface. */
    public static final class ChangedThroughADefaultMethod {

        private ChangedThroughADefaultMethod() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            new DefaultImpl().rewrite(model);
            return AdequacyReport.of(model);
        }
    }

    /** Reads the report of a model and fails before the ask that comes after, where it is caught. */
    public static final class ThrownOnTheReadAndCaughtByTheCaller {

        private ThrownOnTheReadAndCaughtByTheCaller() { }

        private static boolean look(Compilation model) {
            AdequacyReport report = AdequacyReport.of(model);
            if (report == null) {
                throw new IllegalStateException("none");
            }
            TheDoor.compiles(model);
            return true;
        }

        public static boolean read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            try {
                return look(model);
            } catch (IllegalStateException none) {
                return true;
            }
        }
    }

    /** Keeps the look of a model through a check that the model is there. */
    public static final class RequireNonNullKeepsTheAsk {

        private RequireNonNullKeepsTheAsk() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            Compilation same = Objects.requireNonNull(model);
            return AdequacyReport.of(same);
        }
    }

    /** Code that is not walked, written to change the model it is handed. */
    public static final class ProductionChanger {

        private ProductionChanger() { }

        public static void rewrite(Compilation model) {
            model.update(Map.of(), Set.of(), LocalDate.MIN);
        }
    }

    /** Hands an asked-about model to code that changes it, and reads it. */
    public static final class HandedToCodeThatChangesIt {

        private HandedToCodeThatChangesIt() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            ProductionChanger.rewrite(model);
            return AdequacyReport.of(model);
        }
    }

    /** Reads the report in a method of its own that changes the model and then asks about it. */
    public static final class ReadThenChangedThenAskedInAMethod {

        private ReadThenChangedThenAskedInAMethod() { }

        private static void readThenReplaceAndCheck(Compilation model,
                                                    Map<String, String> replacement) {
            AdequacyReport.of(model);
            model.update(replacement, Set.of(), LocalDate.MIN);
            TheDoor.compiles(model);
        }

        public static void read(String source, Map<String, String> other) {
            readThenReplaceAndCheck(Compilation.ofSource(source, "Main"), other);
        }
    }

    /** Keeps an asked-about model in a field and changes it there. */
    public static final class FieldMutatedAfterTheLook {

        private Compilation model;

        public AdequacyReport read(String source, Map<String, String> other) {
            model = TheDoor.answered(source);
            model.update(other, Set.of(), LocalDate.MIN);
            return AdequacyReport.of(model);
        }
    }

    /** Hands the store of an asked-about model to a method that changes it. */
    public static final class DbHandedToAMethod {

        private DbHandedToAMethod() { }

        private static void replaceText(Db store) {
            store.forget(new SourceId("main.sou"), "main");
        }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            replaceText(model.db());
            return AdequacyReport.of(model);
        }
    }

    /** Changes the store through a variable it was put in. */
    public static final class DbChangedThroughAVariable {

        private DbChangedThroughAVariable() { }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            Db store = model.db();
            store.forget(new SourceId("main.sou"), "main");
            return AdequacyReport.of(model);
        }
    }

    /** Hands the store of an asked-about model to a method that only reads it. */
    public static final class DbHandedToAReader {

        private DbHandedToAReader() { }

        private static boolean holds(Db store) {
            return store.allowances() != null;
        }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            Objects.requireNonNull(Boolean.valueOf(holds(model.db())));
            return AdequacyReport.of(model);
        }
    }

    /** Changes the model and tells the caller it is asked about again. */
    public static final class HelperThatChangesAndAsks {

        private HelperThatChangesAndAsks() { }

        private static Compilation edit(Compilation model, Map<String, String> other) {
            model.update(other, Set.of(), LocalDate.MIN);
            return TheDoor.compiles(model);
        }

        public static AdequacyReport read(String source, Map<String, String> other) {
            Compilation model = TheDoor.answered(source);
            edit(model, other);
            return AdequacyReport.of(model);
        }
    }

    /** Changes a model and fails, and the caller that catches the failure reads the model. */
    public static final class ChangedThenFailedAndCaught {

        private ChangedThenFailedAndCaught() { }

        private static void changeAndFail(Compilation model) {
            model.update(Map.of(), Set.of(), LocalDate.MIN);
            throw new IllegalStateException("changed");
        }

        public static AdequacyReport read(String source) {
            Compilation model = TheDoor.answered(source);
            try {
                changeAndFail(model);
            } catch (IllegalStateException failed) {
                return AdequacyReport.of(model);
            }
            return null;
        }
    }

    /** Marks a method that is no test with something that does not run it. */
    public static final class MarkedAndNotRun {

        private MarkedAndNotRun() { }

        @DisplayName("a report")
        private static AdequacyReport reportOf(Compilation model) {
            return AdequacyReport.of(model);
        }

        public static AdequacyReport read(String source) {
            return reportOf(TheDoor.answered(source));
        }
    }

    /** Says a model is read without compiling it, and reads every report its store holds. */
    public static final class NotCompiledReadsAllReports {

        private NotCompiledReadsAllReports() { }

        public static boolean read(String source) {
            Compilation model = TheDoor.notCompiled(Compilation.ofSource(source, "Main"),
                    "too long");
            return model.db().allReports().isEmpty();
        }
    }

    /** Sets what a model is compiled from through its store before it is asked about. */
    public static final class ConfiguredThroughTheDbBeforeTheLook {

        private ConfiguredThroughTheDbBeforeTheLook() { }

        public static AdequacyReport read(String source) {
            Compilation model = Compilation.ofSource(source, "Main");
            model.db().forget(new SourceId("main.sou"), "main");
            TheDoor.compiles(model);
            return AdequacyReport.of(model);
        }
    }

    /** A method the test engine runs, which a caller also calls with a model that was asked about. */
    @Disabled("a shape written to be read by the check, and never run")
    public static final class EngineHandsItIn {

        private EngineHandsItIn() { }

        @RepeatedTest(1)
        void checks(Compilation model) {
            AdequacyReport.of(model);
        }

        public static void viaACaller(String source) {
            new EngineHandsItIn().checks(TheDoor.answered(source));
        }
    }
}
