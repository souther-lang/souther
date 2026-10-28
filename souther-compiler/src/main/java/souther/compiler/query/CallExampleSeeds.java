package souther.compiler.query;

import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.Sig;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.RowOutcome;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;
import souther.compiler.partition.MeasuredInput;
import souther.compiler.partition.SeedFixtures;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
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
    }

    /**
     * The calls of behaviors that {@code analysis} makes, in the order the body makes them,
     * keeping those of a callee that {@code worthReading} takes. Nothing is read of the input
     * where there is none.
     */
    static List<Call> callsIn(AnalysisBody analysis, InputReading input,
                              Predicate<ValueName.Behavior> worthReading) {
        List<AnOperationApplied> calls = new ArrayList<>();
        collect(analysis.core(), worthReading, calls);
        if (calls.isEmpty()) {
            return List.of();
        }
        InputReads reads = InputReads.ofParametersWhereCallsStand(
                input.domain().parameterReads(), input.declared(),
                ElementBindings.of(analysis, input.newtypes()), input.domain().dependencies());
        List<Call> out = new ArrayList<>();
        for (AnOperationApplied each : calls) {
            List<Optional<TermPath>> at = new ArrayList<>();
            for (Core argument : each.args()) {
                at.add(reads.pathOf(argument, input.newtypes()) instanceof PathResolution.At(
                        TermPath path) ? Optional.of(path) : Optional.empty());
            }
            out.add(new Call((ValueName.Behavior) each.operation(), at));
        }
        return out;
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
    static List<Generator.GeneratedRow> rowsFor(Db db, String module, Sig sig,
                                                MeasuredInput subject, InputReading input,
                                                AnalysisBody analysis, Generator.CandidateCheck check,
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
        List<Call> calls = callsIn(analysis, input, callee -> callee.module().equals(module)
                && sigs.containsKey(callee.name()) && read.byBehavior().get(callee.name()) != null
                && !read.byBehavior().get(callee.name()).ran().isEmpty());
        Map<List<String>, Generator.GeneratedRow> out = new LinkedHashMap<>();
        Set<List<String>> considered = new HashSet<>();
        Map<WrittenRow, List<Optional<FixtureTemplate>>> written = new HashMap<>();
        int tried = 0;
        for (Call call : calls) {
            if (!call.standsAtTheInputThroughout()) {
                continue;
            }
            Sig callee = sigs.get(call.callee().name());
            List<RowOutcome> rows = read.byBehavior().get(call.callee().name()).ran();
            for (int at = 0; at < rows.size(); at++) {
                RowOutcome row = rows.get(at);
                if (row.inputs().size() != call.at().size()) {
                    continue;
                }
                if (tried++ == limit) {
                    return List.copyOf(out.values());
                }
                List<Optional<FixtureTemplate>> inputsWritten = written.computeIfAbsent(
                        new WrittenRow(call.callee(), at), _ -> writtenInputs(row, callee, subject));
                Optional<Map<Integer, FixtureTemplate>> lifted =
                        lifted(call, inputsWritten, subject);
                if (lifted.isEmpty()) {
                    continue;
                }
                List<FixtureTemplate> inputs = new ArrayList<>(base == null
                        ? Collections.nCopies(subject.parameters().size(), null) : base.inputs());
                lifted.get().forEach(inputs::set);
                List<String> key = inputs.stream()
                        .map(each -> each == null ? null : each.text()).toList();
                if (inputs.contains(null) || !considered.add(key)
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
     * element it stands under. Nothing where an argument stands anywhere else, where two stand
     * at one parameter, or where an input could not be written.
     */
    private static Optional<Map<Integer, FixtureTemplate>> lifted(
            Call call, List<Optional<FixtureTemplate>> written, MeasuredInput subject) {
        Map<Integer, FixtureTemplate> out = new LinkedHashMap<>();
        for (int i = 0; i < call.at().size(); i++) {
            TermPath at = call.at().get(i).orElseThrow();
            int parameter = subject.parameters().indexOf(at.head());
            if (parameter < 0 || written.get(i).isEmpty()
                    || !at.steps().stream().allMatch(step -> step instanceof TermPath.Step.Element)) {
                return Optional.empty();
            }
            FixtureTemplate held = written.get(i).get();
            for (int depth = 0; depth < at.steps().size(); depth++) {
                held = FixtureTemplate.collection(List.of(held));
            }
            if (out.putIfAbsent(parameter, held) != null) {
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

    private static void collect(Core e, Predicate<ValueName.Behavior> worthReading,
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
