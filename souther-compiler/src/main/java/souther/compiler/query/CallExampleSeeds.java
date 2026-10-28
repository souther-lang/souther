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
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The inputs of the behaviors a behavior calls, which its own rows can be tried with.
 *
 * <p>A behavior a body calls has rows of its own, and the values those rows hand it are values a
 * caller is worth trying: the author reached for them. They say nothing about what the caller owes
 * — no obligation of the caller's is made of them — and nothing about what the caller answers.
 * This reads where a call stands in the caller's input; what is built from it is somebody else's.
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
    }

    /** The calls of behaviors that {@code analysis} makes, in the order the body makes them. */
    static List<Call> callsIn(AnalysisBody analysis, InputReading input) {
        var newtypes = input.newtypes();
        InputReads reads = InputReads.ofParametersWhereCallsStand(
                input.domain().parameterReads(), input.declared(),
                ElementBindings.of(analysis, newtypes), input.domain().dependencies());
        List<Call> out = new ArrayList<>();
        walk(analysis.core(), reads, input, out);
        return out;
    }

    /**
     * The rows of the caller that hand each call the inputs a row of its callee gives.
     *
     * <p>Direct calls only, in the order the body makes them, and each row of the callee in the
     * order it is written. A row of the callee is read at its inputs: a call whose argument stands
     * at an element of a list the caller takes is handed a list holding that one input, and one
     * whose argument stands at the parameter itself is handed the input. Every other position of
     * the caller's input is whatever {@code bases} first composed, so a row seeded here differs
     * from it at the positions the call reads and nowhere else.
     *
     * <p>What the callee's row answers is no part of this, and neither is what the caller owes:
     * these rows are inputs to try. A candidate the decoder refuses, an input nothing can write,
     * or a callee of another module is no row.
     *
     * @param bases the rows composed for the caller already, whose first stands the positions no
     *              call reads
     * @param limit how many rows at most
     */
    static List<Generator.GeneratedRow> rowsFor(Db db, String module, Sig sig,
                                                MeasuredInput subject, InputReading input,
                                                AnalysisBody analysis, Generator.CandidateCheck check,
                                                List<Generator.GeneratedRow> bases,
                                                boolean standsNothingIn, int limit) {
        Output.RowsRead.Of read = db.ask(new Output.RowsRead(module)).value();
        Map<String, Sig> sigs = db.ask(new Bodies.Signatures(module)).value();
        if (read == null || sigs == null) {
            return List.of();
        }
        Generator.GeneratedRow base = bases.isEmpty() ? null : bases.getFirst();
        // The positions no call reads, and what a dependency of the behavior is stood in with, are
        // the base's. Without one, a behavior taking a single input and standing nothing in is
        // still a row: the input is all of it.
        if (base == null && !(standsNothingIn && subject.parameters().size() == 1)) {
            return List.of();
        }
        Map<List<String>, Generator.GeneratedRow> out = new LinkedHashMap<>();
        for (Call call : callsIn(analysis, input)) {
            Output.RowsRead.ReadRows its = read.byBehavior().get(call.callee().name());
            Sig callee = sigs.get(call.callee().name());
            if (!call.callee().module().equals(module) || its == null || callee == null) {
                continue;
            }
            for (RowOutcome row : its.ran()) {
                if (row.inputs().size() != call.at().size()) {
                    continue;
                }
                List<FixtureTemplate> inputs = new ArrayList<>(base == null
                        ? Collections.nCopies(1, null) : base.inputs());
                if (seeded(inputs, call, row, callee, subject, check)
                        && !inputs.contains(null)) {
                    List<String> key = inputs.stream().map(FixtureTemplate::text).toList();
                    out.putIfAbsent(key, new Generator.GeneratedRow(
                            List.of(new Generator.Purpose.Unstated()), inputs,
                            base == null ? List.of() : base.answers()));
                }
                if (out.size() >= limit) {
                    return List.copyOf(out.values());
                }
            }
        }
        return List.copyOf(out.values());
    }

    /** Whether each position {@code call} reads was set in {@code inputs} to what {@code row}
     *  gave it, and the decoder took it. */
    private static boolean seeded(List<FixtureTemplate> inputs, Call call, RowOutcome row,
                                  Sig callee, MeasuredInput subject,
                                  Generator.CandidateCheck check) {
        Set<Integer> set = new HashSet<>();
        for (int i = 0; i < call.at().size(); i++) {
            if (call.at().get(i).isEmpty()) {
                continue;
            }
            TermPath at = call.at().get(i).get();
            int parameter = subject.parameters().indexOf(at.head());
            if (parameter < 0 || !set.add(parameter)
                    || !at.steps().stream().allMatch(step -> step instanceof TermPath.Step.Element)) {
                return false;
            }
            Optional<FixtureTemplate> written = SeedFixtures.written(row.inputs().get(i),
                    callee.ins().get(i).type(), subject.ruleReading());
            if (written.isEmpty()) {
                return false;
            }
            FixtureTemplate candidate = written.get();
            for (int depth = 0; depth < at.steps().size(); depth++) {
                candidate = FixtureTemplate.collection(List.of(candidate));
            }
            if (check.refuse(parameter, candidate).isPresent()) {
                return false;
            }
            inputs.set(parameter, candidate);
        }
        return !set.isEmpty();
    }

    private static void walk(Core e, InputReads reads, InputReading input, List<Call> out) {
        for (Core each : Core.subexpressionsAt(e)) {
            if (AnOperationApplied.of(each) instanceof AnOperationApplied applied
                    && applied.operation() instanceof ValueName.Behavior callee) {
                List<Optional<TermPath>> at = new ArrayList<>();
                for (Core argument : applied.args()) {
                    at.add(reads.pathOf(argument, input.newtypes()) instanceof PathResolution.At(
                            TermPath path) ? Optional.of(path) : Optional.empty());
                }
                out.add(new Call(callee, at));
            }
        }
        Core.forEachChild(e, child -> walk(child, reads, input, out));
    }
}
