package souther.compiler.query;

import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.FakeTables;
import souther.compiler.check.ScopeStep;
import souther.compiler.check.Sig;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.RowStatement;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;
import souther.compiler.partition.MeasuredInput;
import souther.compiler.partition.SeedFixtures;
import souther.compiler.partition.StoodInAnswer;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * The rows of a behavior that try it with the inputs the rows of the behaviors it calls give.
 *
 * <p>A behavior a body calls has rows of its own, and the values those rows hand it are values a
 * caller is worth trying: the author reached for them. They say nothing about what the caller owes
 * — no obligation of the caller's is made of them — and nothing about what the caller answers.
 *
 * <p>A row of the callee is lifted whole or not at all. The lift is the one function that says
 * which inputs of the caller make the call hand its callee that row's inputs, and it has an answer
 * only where every argument of the call stands at a position of the caller's input: an argument
 * that stands at none is a value the caller computes, so the row the caller would run is not the
 * callee's. What is built from a lift — the positions it does not read, what the decoder takes —
 * is assembled after it and never decides it. Whether the call is reached by the row is not
 * claimed: a seeded row is an input to try.
 */
final class CallExampleSeeds {

    private CallExampleSeeds() {}

    /**
     * One call of a behavior in a caller's body.
     *
     * @param callee the behavior called
     * @param at     where each argument stands in the caller's input, empty where it stands at none
     */
    record Call(ValueName.Behavior callee, List<Optional<TermPath>> at) {

        Call {
            at = List.copyOf(at);
        }

        /** Whether every argument stands at a position of the caller's input, which is what a row
         *  of the callee can be lifted through. */
        boolean standsAtTheInputThroughout() {
            return at.stream().allMatch(Optional::isPresent);
        }

        /** Whether a lift through this call asks the generator to build a value, which an
         *  argument at a field or a case does and one at an element or a parameter does not. */
        boolean buildsAroundAPosition() {
            return at.stream().anyMatch(each -> each.orElseThrow().steps().stream()
                    .anyMatch(step -> !(step instanceof TermPath.Step.Element)));
        }
    }

    /**
     * The calls of behaviors that {@code analysis} makes, each once, in the order the body first
     * makes it, keeping those of a callee that {@code worthReading} takes. A call written twice
     * with the same arguments hands its callee the same rows twice, so it is one call. Nothing is
     * read of the input where there is none.
     */
    static List<Call> callsIn(AnalysisBody analysis, InputReading input,
                              Predicate<ValueName.Behavior> worthReading) {
        List<AnOperationApplied> any = new ArrayList<>();
        collect(analysis.core(), worthReading, any);
        if (any.isEmpty()) {
            return List.of();
        }
        InputReads reads = InputReads.ofParametersWhereCallsStand(
                input.domain().parameterReads(), input.declared(),
                ElementBindings.of(analysis, input.newtypes()), input.domain().dependencies());
        List<CallRead> calls = new ArrayList<>();
        collect(analysis.core(), reads, input, worthReading, calls);
        Set<Call> out = new LinkedHashSet<>();
        for (CallRead each : calls) {
            List<Optional<TermPath>> at = new ArrayList<>();
            for (Core argument : each.applied().args()) {
                at.add(each.reads().pathOf(argument, input.newtypes()) instanceof PathResolution.At(
                        TermPath path) ? Optional.of(path) : Optional.empty());
            }
            out.add(new Call((ValueName.Behavior) each.applied().operation(), at));
        }
        return List.copyOf(out);
    }

    /** A call of a behavior, with the reading of the names in force where it is made. */
    private record CallRead(AnOperationApplied applied, InputReads reads) {}

    /**
     * The calls under {@code e}, each with the reading of the names in force at it: a name an arm
     * binds over a case, or a {@code let} binds, stands for a position of the input only in the
     * reading the arm or the {@code let} is entered in.
     */
    private static void collect(Core e, InputReads reads, InputReading input,
                                Predicate<ValueName.Behavior> worthReading, List<CallRead> out) {
        for (Core each : Core.subexpressionsAt(e)) {
            if (AnOperationApplied.of(each) instanceof AnOperationApplied applied
                    && applied.operation() instanceof ValueName.Behavior callee
                    && worthReading.test(callee)) {
                out.add(new CallRead(applied, reads));
            }
        }
        ScopeStep.forEachChild(e, (child, step) -> collect(child,
                input.symbols() == null ? reads
                        : reads.entering(step, input.symbols(), input.newtypes()),
                input, worthReading, out));
    }

    /**
     * The rows of the caller that hand each call the inputs a row of its callee gives.
     *
     * <p>Direct calls only, in the order the body makes them, and each row of the callee in the
     * order it is written. A call whose argument stands at an element of a list the caller takes
     * is handed a list holding that one input, and one whose argument stands at the parameter
     * itself is handed the input. Every position of the caller's input no argument stands at is
     * what the first of {@code bases} has there, or nothing is composed where there is no base and
     * the callee's row does not fill them all.
     *
     * <p>A row the caller has written is not offered again, and the first lift to it takes none of
     * the rows tried: it costs no build. It is the same row when its inputs are the inputs of the written one and
     * both are answered by the module's table for each dependency; a written row with a
     * {@code with} of its own, or a base that answers with a value of its own, is not compared
     * and the row is offered.
     *
     * <p>What the callee's row answers is no part of this, and neither is what the caller owes:
     * these rows are inputs to try. A candidate the decoder refuses, an input nothing can write,
     * or a callee of another module is no row.
     *
     * <p><b>At most {@code limit} rows of callees are tried.</b> Tried, and not only taken: a row
     * the decoder refuses costs a build as one it takes does, so a bound on the rows taken would
     * leave the work unbounded wherever the callees' rows are refused. Rows past it are not looked
     * at, which says nothing about them.
     *
     * @param bases          the rows composed for the caller already
     * @param standsNothingIn whether the caller has no dependency to stand in, which is what lets a
     *                       row be composed without a base to take the stand-ins from
     * @param limit          how many rows of callees at most are tried
     */
    static List<Generator.GeneratedRow> rowsFor(Db db, String module, MeasuredInput subject,
                                                InputReading input, AnalysisBody analysis,
                                                Generator.CandidateCheck check,
                                                List<Generator.GeneratedRow> bases,
                                                boolean standsNothingIn, int limit) {
        Generator.GeneratedRow base = bases.isEmpty() ? null : bases.getFirst();
        if (base == null && !standsNothingIn) {
            return List.of();
        }
        Output.RowsRead.Of read = db.ask(new Output.RowsRead(module)).value();
        Map<String, Sig> sigs = db.ask(new Bodies.Signatures(module)).value();
        if (read == null || sigs == null) {
            return List.of();
        }
        // The rows that ran, worked out from a callee's rows once however many calls name it:
        // that is a walk over all of them each time it is asked.
        Map<String, List<RowOutcome>> ran = new HashMap<>();
        Function<String, List<RowOutcome>> ranOf = name -> ran.computeIfAbsent(name,
                _ -> read.byBehavior().get(name) == null ? List.of()
                        : read.byBehavior().get(name).ran());
        List<Call> calls = callsIn(analysis, input, callee -> callee.module().equals(module)
                && sigs.containsKey(callee.name()) && !ranOf.apply(callee.name()).isEmpty());
        if (calls.stream().noneMatch(Call::standsAtTheInputThroughout)) {
            return List.of();
        }
        Map<List<String>, Generator.GeneratedRow> out = new LinkedHashMap<>();
        Set<List<String>> alreadyWritten = writtenByTheCaller(
                ranOf.apply(subject.behavior()), sigs.get(subject.behavior()), subject,
                base == null ? List.of() : base.answers(),
                db.ask(new Names.FakeTables(module)).value());
        Set<List<String>> considered = new HashSet<>();
        Map<WrittenRow, List<Optional<FixtureTemplate>>> written = new HashMap<>();
        int tried = 0;
        for (Call call : calls) {
            if (!call.standsAtTheInputThroughout()) {
                continue;
            }
            Sig callee = sigs.get(call.callee().name());
            List<RowOutcome> rows = ranOf.apply(call.callee().name());
            for (int at = 0; at < rows.size(); at++) {
                RowOutcome row = rows.get(at);
                if (row.inputs().size() != call.at().size()) {
                    continue;
                }
                List<Optional<FixtureTemplate>> inputsWritten = written.computeIfAbsent(
                        new WrittenRow(call.callee(), at), _ -> writtenInputs(row, callee, subject));
                // A lift that builds around a position asks the decoder before the key is known,
                // so it is a row tried whether or not the author wrote it.
                boolean counted = call.buildsAroundAPosition();
                if (counted && tried++ == limit) {
                    return List.copyOf(out.values());
                }
                Optional<Map<Integer, FixtureTemplate>> lifted =
                        lifted(call, inputsWritten, subject, check);
                List<FixtureTemplate> inputs = lifted.isEmpty() ? List.of()
                        : composed(base, lifted.get(), subject);
                List<String> key = inputs.stream()
                        .map(each -> each == null ? null : each.text()).toList();
                // A row the author has written costs no build, so the first lift to it takes none
                // of the rows tried, and the rows looked at past the limit are no more than the
                // rows the author wrote. It is considered at once, so a later lift to it takes a
                // row tried and is never offered.
                if (lifted.isPresent() && alreadyWritten.contains(key) && considered.add(key)) {
                    continue;
                }
                if (!counted && tried++ == limit) {
                    return List.copyOf(out.values());
                }
                if (lifted.isEmpty() || inputs.contains(null) || !considered.add(key)
                        || refused(lifted.get(), check)) {
                    continue;
                }
                out.put(key, new Generator.GeneratedRow(
                        List.of(new Generator.Purpose.Unstated()), inputs,
                        base == null ? List.of() : base.answers()));
            }
        }
        return List.copyOf(out.values());
    }

    /** One row of one callee, by its place among the callee's rows, which is what a written input
     *  is a function of. */
    private record WrittenRow(ValueName.Behavior callee, int place) {}

    /** The inputs of the row a lift makes: the base's, with the lifted ones put in place. */
    private static List<FixtureTemplate> composed(Generator.GeneratedRow base,
                                                  Map<Integer, FixtureTemplate> lifted,
                                                  MeasuredInput subject) {
        List<FixtureTemplate> inputs = new ArrayList<>(base == null
                ? Collections.nCopies(subject.parameters().size(), null) : base.inputs());
        lifted.forEach(inputs::set);
        return inputs;
    }

    /**
     * The inputs, as the text a row of the caller carries them in, of each row the caller has
     * written that a seed stands in for the dependencies in the same way as.
     *
     * <p>A seed takes the stand-ins of its base, so it is the row the author wrote only when the
     * author's row is answered by the same. Where the base leans on the module's table, that is a
     * written row whose every dependency is answered by the table the module declares for it and
     * not by a {@code with}. A base that answers a dependency with a value of its own is not
     * compared: whether that is the value a written row states is not read here, and a row not
     * known to be written is offered. A row with an input that cannot be written is left out too.
     */
    private static Set<List<String>> writtenByTheCaller(List<RowOutcome> rows, Sig caller,
                                                        MeasuredInput subject,
                                                        List<StoodInAnswer> answers,
                                                        FakeTables declared) {
        Set<List<String>> out = new HashSet<>();
        if (caller == null || declared == null
                || !answers.stream().allMatch(StoodInAnswer.InTheModule.class::isInstance)) {
            return out;
        }
        for (RowOutcome row : rows) {
            if (row.inputs().size() != caller.ins().size()
                    || !leansOnTheModule(row, declared)) {
                continue;
            }
            List<Optional<FixtureTemplate>> inputs = writtenInputs(row, caller, subject);
            if (inputs.stream().allMatch(Optional::isPresent)) {
                out.add(inputs.stream().map(each -> each.get().text()).toList());
            }
        }
        return out;
    }

    /** Whether every dependency {@code row} states is answered by the table the module declares
     *  for it, which is where a row is written that has no {@code with} for it. */
    private static boolean leansOnTheModule(RowOutcome row, FakeTables declared) {
        if (!(row.statement() instanceof RowStatement.Stated stated)) {
            return false;
        }
        return stated.standIns().stream().allMatch(each ->
                declared.declaredFor(each.dependency()) instanceof
                        FakeTables.Declaration.One(FakeTables.Occurrence.Resolved table)
                        && declared.writtenAt(each.at()).filter(table::equals).isPresent());
    }

    /** What each input of {@code row} is written as, empty where it cannot be. */
    private static List<Optional<FixtureTemplate>> writtenInputs(RowOutcome row, Sig callee,
                                                                 MeasuredInput subject) {
        List<Optional<FixtureTemplate>> out = new ArrayList<>();
        for (int i = 0; i < row.inputs().size(); i++) {
            out.add(SeedFixtures.written(row.inputs().get(i), callee.ins().get(i).type(),
                    subject.ruleReading()));
        }
        return out;
    }

    /**
     * What each parameter of the caller is to hold for the call to be handed {@code written}: the
     * value an argument stands at the parameter itself for, and a list of one of it for each
     * element it stands under. Nothing where an argument stands anywhere else, where two
     * arguments stand at one parameter and the row gives them different values, or where an input
     * could not be written.
     *
     * <p>An argument that stands at a field of the input, or at a value narrowed by {@code as}, is
     * a position the row's value is fixed at and not a value the lift builds: the record and the
     * case around it are what the model builds ({@link Generator#composeWithFixedValues}).
     */
    private static Optional<Map<Integer, FixtureTemplate>> lifted(
            Call call, List<Optional<FixtureTemplate>> written, MeasuredInput subject,
            Generator.CandidateCheck check) {
        Map<Integer, FixtureTemplate> out = new LinkedHashMap<>();
        Map<TermPath, FixtureTemplate> fixed = new LinkedHashMap<>();
        for (int i = 0; i < call.at().size(); i++) {
            TermPath at = call.at().get(i).orElseThrow();
            int parameter = subject.parameters().indexOf(at.head());
            if (parameter < 0 || written.get(i).isEmpty()) {
                return Optional.empty();
            }
            FixtureTemplate held = written.get(i).get();
            if (!at.steps().stream().allMatch(step -> step instanceof TermPath.Step.Element)) {
                // One position holds one value, as below.
                FixtureTemplate already = fixed.putIfAbsent(at, held);
                if (already != null && !already.text().equals(held.text())) {
                    return Optional.empty();
                }
                continue;
            }
            for (int depth = 0; depth < at.steps().size(); depth++) {
                held = FixtureTemplate.collection(List.of(held));
            }
            // One position holds one value: two arguments standing at it are served by it when the
            // row gives them the same, and by no value when it gives them two.
            FixtureTemplate already = out.putIfAbsent(parameter, held);
            if (already != null && !already.text().equals(held.text())) {
                return Optional.empty();
            }
        }
        if (fixed.isEmpty()) {
            return Optional.of(out);
        }
        Optional<Map<Integer, FixtureTemplate>> built =
                Generator.composeWithFixedValues(subject, fixed, check);
        if (built.isEmpty()) {
            return Optional.empty();
        }
        for (Map.Entry<Integer, FixtureTemplate> each : built.get().entrySet()) {
            if (out.putIfAbsent(each.getKey(), each.getValue()) != null) {
                return Optional.empty();
            }
        }
        return Optional.of(out);
    }

    /** Whether the decoder refuses one of the values a lift puts at a parameter. */
    private static boolean refused(Map<Integer, FixtureTemplate> lifted,
                                   Generator.CandidateCheck check) {
        return lifted.entrySet().stream()
                .anyMatch(each -> check.refuse(each.getKey(), each.getValue()).isPresent());
    }

    static void collect(Core e, Predicate<ValueName.Behavior> worthReading,
                        List<AnOperationApplied> out) {
        for (Core each : Core.subexpressionsAt(e)) {
            if (AnOperationApplied.of(each) instanceof AnOperationApplied applied
                    && applied.operation() instanceof ValueName.Behavior callee
                    && worthReading.test(callee)) {
                out.add(applied);
            }
        }
        Core.forEachChild(e, child -> collect(child, worthReading, out));
    }
}
