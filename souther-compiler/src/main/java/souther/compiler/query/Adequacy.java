package souther.compiler.query;

import souther.compiler.ast.Ast;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.InputCaseEvidence;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.observe.OutputCaseEvidence;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.Stage;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** How well a module's {@code example} rows cover what it declares. */
public final class Adequacy {

    /** What the rows say about one behavior's signature. */
    public record SignatureEvidence(OutputCaseEvidence output, List<InputCaseEvidence> inputs,
                                    MeasurementStatus status) {
        public SignatureEvidence {
            inputs = List.copyOf(inputs);
        }
    }

    /**
     * The signature evidence for every behavior of one module.
     *
     * <p>A module's question, not a source's, although the rows are evaluated per source. A behavior's
     * rows are written across the module's own file and any number of attached {@code examples for}
     * files, so asking this of one source at a time would report the cases the other files cover as
     * uncovered. The per-source answers are read for their values and united here; no row is run twice.
     */
    public record Witnesses(String name) implements Key<Map<String, SignatureEvidence>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, SignatureEvidence>> compute(Db db) {
            Answer<Ast.Module> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(name));
            if (!prepared.present() || !scope.present() || !sigs.present()) {
                return Answer.absent();
            }
            Map<String, List<RowOutcome>> byTarget = rowsByTarget(db, name);
            Map<String, SignatureEvidence> out = new LinkedHashMap<>();
            for (Ast.BehaviorDef behavior : prepared.value().behaviors()) {
                Sig sig = sigs.value().get(behavior.name());
                if (sig == null) {
                    continue;   // a behavior whose signature did not work out has nothing to measure
                }
                out.put(behavior.name(), evidenceOf(sig, scope.value(),
                        byTarget.getOrDefault(behavior.name(), List.of())));
            }
            return Answer.of(Map.copyOf(out));
        }

        /** Every row this module's sources observed, grouped by the behavior it is about. */
        private Map<String, List<RowOutcome>> rowsByTarget(Db db, String module) {
            List<String> origins = db.ask(new Front.ExampleOrigins(module)).value();
            Map<String, List<RowOutcome>> byTarget = new LinkedHashMap<>();
            if (origins == null) {
                return byTarget;
            }
            Set<String> sources = new LinkedHashSet<>(origins);
            for (String sourceId : sources) {
                Output.Examples.Of observed =
                        db.ask(new Output.Examples(module, sourceId)).value();
                if (observed == null) {
                    continue;
                }
                for (RowOutcome row : observed.rows()) {
                    byTarget.computeIfAbsent(row.target(), _ -> new ArrayList<>()).add(row);
                }
            }
            return byTarget;
        }
    }

    /**
     * What every behavior of one module reaches of the distinctions its model draws.
     *
     * <p>A module's question for the same reason the witnesses are: a behavior's rows are written
     * across its own source and any attached files, and a class covered in one of them is covered.
     */
    public record Coverage(String name) implements Key<Map<String, PartitionEvidence>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, PartitionEvidence>> compute(Db db) {
            Answer<Ast.Module> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(name));
            if (!prepared.present() || !scope.present() || !sigs.present()) {
                return Answer.absent();
            }
            souther.compiler.check.TypeChecker.Checked checked =
                    db.ask(new Bodies.Checked(name)).value();
            Map<String, souther.compiler.core.Core> bodies =
                    checked == null ? Map.of() : checked.behaviorBodies();
            souther.compiler.coverage.CoverageSites.Plan plan =
                    souther.compiler.coverage.CoverageSites.of(sourceIdOf(db, name), bodies);
            Map<String, List<RowOutcome>> byTarget = rowsOf(db, name);

            Map<String, PartitionEvidence> out = new LinkedHashMap<>();
            for (Ast.BehaviorDef behavior : prepared.value().behaviors()) {
                if (!(behavior instanceof Ast.SpecBehavior spec)) {
                    continue;   // a composition's inputs are its first stage's, measured there
                }
                Sig sig = sigs.value().get(spec.name());
                if (sig == null) {
                    continue;
                }
                out.put(spec.name(), Coverages.of(spec, sig, scope.value(), bodies.get(spec.name()),
                        plan, byTarget.getOrDefault(spec.name(), List.of())));
            }
            return Answer.of(Map.copyOf(out));
        }

        private static String sourceIdOf(Db db, String module) {
            Front.Layout.Of layout = db.ask(new Front.Layout()).value();
            return layout == null ? module : layout.idOfModule().getOrDefault(module, module);
        }

        private static Map<String, List<RowOutcome>> rowsOf(Db db, String module) {
            List<String> origins = db.ask(new Front.ExampleOrigins(module)).value();
            Map<String, List<RowOutcome>> byTarget = new LinkedHashMap<>();
            if (origins == null) {
                return byTarget;
            }
            for (String sourceId : new LinkedHashSet<>(origins)) {
                Output.Examples.Of observed = db.ask(new Output.Examples(module, sourceId)).value();
                if (observed == null) {
                    continue;
                }
                for (RowOutcome row : observed.rows()) {
                    byTarget.computeIfAbsent(row.target(), _ -> new ArrayList<>()).add(row);
                }
            }
            return byTarget;
        }
    }

    /**
     * What a behavior's rows establish about its signature.
     *
     * <p>Which set a row lands in is decided by how far it got, never by whether it passed. A row that
     * disagreed still applied the behavior and still saw an answer, and a coverage measure that dropped
     * it would report the case it produced as one nothing produces.
     */
    /**
     * The cases a position has to be covered at, which is not quite what a row's expected arm is held
     * against ({@link TypeOps#outputCases}).
     *
     * <p>A position typed as one data has one case, and covering it is not a question: any row at all
     * covers it, so reporting {@code 1/1} everywhere adds a number that is never anything else. What
     * is worth counting is a position that can be more than one thing. The arm check is wider on
     * purpose — it uses the single name to catch a row that wrote the wrong one.
     */
    private static Set<TypeName> coverableCases(Type t, Symbols symbols) {
        return TypeOps.isSumType(t, symbols) ? TypeOps.leafCases(t, symbols) : Set.of();
    }

    static SignatureEvidence evidenceOf(Sig sig, Symbols symbols, List<RowOutcome> rows) {
        Set<TypeName> declaredOut = coverableCases(sig.out(), symbols);
        Set<TypeName> specified = new LinkedHashSet<>();
        Set<TypeName> observed = new LinkedHashSet<>();
        Set<TypeName> verified = new LinkedHashSet<>();
        int unreadableOut = 0;

        List<Type> ins = sig.ins();
        List<Set<TypeName>> declaredIn = new ArrayList<>(ins.size());
        List<Set<TypeName>> inSpecified = new ArrayList<>(ins.size());
        List<Set<TypeName>> inExecuted = new ArrayList<>(ins.size());
        List<Set<TypeName>> inVerified = new ArrayList<>(ins.size());
        int[] unreadableIn = new int[ins.size()];
        for (Type in : ins) {
            declaredIn.add(coverableCases(in, symbols));
            inSpecified.add(new LinkedHashSet<>());
            inExecuted.add(new LinkedHashSet<>());
            inVerified.add(new LinkedHashSet<>());
        }

        for (RowOutcome row : rows) {
            boolean held = row.disposition() == Disposition.HELD;
            if (row.expectedArm() != null) {
                specified.add(row.expectedArm());
            } else if (!declaredOut.isEmpty()) {
                unreadableOut++;   // an expectation whose case the text does not say
            }
            if (row.resultArm() != null) {
                observed.add(row.resultArm());
                if (held) {
                    verified.add(row.resultArm());
                }
            }
            for (int i = 0; i < ins.size(); i++) {
                if (declaredIn.get(i).isEmpty()) {
                    continue;   // not a sum: nothing to cover at this position
                }
                TypeName written = i < row.inputCases().size() ? row.inputCases().get(i) : null;
                if (written == null) {
                    unreadableIn[i]++;
                    continue;
                }
                if (row.stage().reached(Stage.FIXTURES_VALIDATED)) {
                    inSpecified.get(i).add(written);
                }
                if (row.stage().reached(Stage.INVOKED)) {
                    inExecuted.get(i).add(written);
                }
                if (held) {
                    inVerified.get(i).add(written);
                }
            }
        }

        OutputCaseEvidence output = declaredOut.isEmpty() ? OutputCaseEvidence.none()
                : new OutputCaseEvidence(declaredOut, specified, observed, verified, unreadableOut);
        List<InputCaseEvidence> inputs = new ArrayList<>(ins.size());
        boolean partial = output.status() == MeasurementStatus.PARTIAL;
        for (int i = 0; i < ins.size(); i++) {
            InputCaseEvidence evidence = declaredIn.get(i).isEmpty() ? InputCaseEvidence.none()
                    : new InputCaseEvidence(declaredIn.get(i), inSpecified.get(i), inExecuted.get(i),
                            inVerified.get(i), unreadableIn[i]);
            inputs.add(evidence);
            partial |= evidence.status() == MeasurementStatus.PARTIAL;
        }
        // Nothing was measured where nothing was written: a behavior with no rows has no gaps to
        // report, only an absence of evidence, and saying so is not the same as saying it is covered.
        MeasurementStatus status = rows.isEmpty() ? MeasurementStatus.UNAVAILABLE
                : partial ? MeasurementStatus.PARTIAL : MeasurementStatus.COMPLETE;
        return new SignatureEvidence(output, inputs, status);
    }

    private Adequacy() {}
}
