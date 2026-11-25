package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.Codecs;
import souther.compiler.DefaultStdlib;
import souther.compiler.Emitted;
import souther.compiler.KeptCalls;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.execute.RunStop;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ApplicationOrigin;
import souther.compiler.types.FixtureReferenceOrigin;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a call of an operation the library defines by cases folds to, over constants, is what the
 * program answers for the same arguments — and nothing where the program stops.
 *
 * <p>Every such operation over whole numbers, so the day one is added it is held here without
 * being named. The program is the library's own body compiled and run, which is what the cases
 * are a reading of: a fold that took a case for the wrong arguments, or answered past the end of
 * an {@code Int}, answers what the program does not.
 */
class AFoldOfAnOperationDefinedByCasesAnswersWhatTheProgramAnswersTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    /** Each end of an {@code Int}, nought, and either side of it. */
    private static final List<Long> NUMBERS = List.of(Long.MIN_VALUE, -1L, 0L, 1L,
            Long.MAX_VALUE);

    private static final List<String> PLACES = List.of("a", "b", "c");

    @Test
    void aFoldAnswersWhatTheProgramAnswers() throws Exception {
        List<ValueName.Stdlib.Operation> operations = new ArrayList<>();
        for (ValueName each : DischargeRules.definedByCases()) {
            if (each instanceof ValueName.Stdlib.Operation operation
                    && overWholeNumbers(operation)) {
                operations.add(operation);
            }
        }
        assertTrue(operations.stream().anyMatch(each -> each.name().equals("abs")),
                "Int.abs, which answers arithmetic over its argument, is among them: "
                        + operations);
        StringBuilder model = new StringBuilder("""
                module demo

                data In = { a: Int, b: Int, c: Int }
                data Out = Int
                """);
        for (int at = 0; at < operations.size(); at++) {
            ValueName.Stdlib.Operation operation = operations.get(at);
            int arity = entryOf(operation).signature().params().size();
            model.append("""

                    behavior b%d : (i: In) -> Out
                    let b%d (i) = Out { value = %s.%s(%s) }
                    """.formatted(at, at, operation.alias(), operation.name(),
                    String.join(", ", PLACES.subList(0, arity).stream()
                            .map(place -> "i." + place).toList())));
        }
        ClassLoader loader = ACompiledModel.compiles(Compilation.ofSources(
                List.of(model.toString()), ModulePath.EMPTY)).loader();
        CoreConstantEval fold = CoreConstantEval.against(Symbols.none(DefaultStdlib.get()),
                Denotations.none());

        Map<String, String> wrong = new LinkedHashMap<>();
        for (int at = 0; at < operations.size(); at++) {
            ValueName.Stdlib.Operation operation = operations.get(at);
            Object behavior = Emitted.behavior(loader, "demo", "b" + at).getConstructor()
                    .newInstance();
            int arity = entryOf(operation).signature().params().size();
            for (List<Long> args : everyChoiceOf(arity)) {
                Map<String, Object> in = new LinkedHashMap<>();
                for (int place = 0; place < PLACES.size(); place++) {
                    in.put(PLACES.get(place), place < arity ? args.get(place) : 0L);
                }
                Optional<Object> answered;
                try {
                    answered = Optional.of(Codecs.encode(loader, "demo.Out", Codecs.apply(
                            behavior, Codecs.decoded(loader, "demo.In", in))));
                } catch (RuntimeException stopped) {
                    if (RunStop.ofTheEndOf(stopped).isEmpty()) {
                        throw stopped;
                    }
                    answered = Optional.empty();
                }
                Optional<Object> folded = fold.eval(callTo(operation, args));
                if (!folded.equals(answered)) {
                    wrong.put(operation.alias() + "." + operation.name() + args,
                            "folds to " + folded + ", runs to " + answered);
                }
            }
        }
        assertEquals(Map.of(), wrong);
    }

    private static boolean overWholeNumbers(ValueName.Stdlib.Operation operation) {
        Stdlib.Entry entry = entryOf(operation);
        return entry.signature().result() == Type.INT
                && entry.signature().params().stream().allMatch(Type.INT::equals);
    }

    private static Stdlib.Entry entryOf(ValueName.Stdlib.Operation operation) {
        return DefaultStdlib.get().entry(operation);
    }

    /** Every list of {@code arity} of {@link #NUMBERS}. */
    private static List<List<Long>> everyChoiceOf(int arity) {
        List<List<Long>> out = new ArrayList<>(List.of(List.of()));
        for (int place = 0; place < arity; place++) {
            List<List<Long>> next = new ArrayList<>();
            for (List<Long> sofar : out) {
                for (Long number : NUMBERS) {
                    List<Long> one = new ArrayList<>(sofar);
                    one.add(number);
                    next.add(one);
                }
            }
            out = next;
        }
        return out;
    }

    /** A call to {@code operation} over the constants {@code args}. */
    private static Core.PreservedCall callTo(ValueName.Stdlib.Operation operation,
                                             List<Long> args) {
        List<Core> written = new ArrayList<>();
        args.forEach(each -> written.add(new Core.Int(each, Type.INT, POS)));
        return new Core.PreservedCall(KeptCalls.declared(operation), written,
                new Core.KeptCallPlace(new FixtureReferenceOrigin(0),
                        new ApplicationOrigin.ComposedFixture(), OccurrenceLineage.ORIGINAL),
                Core.KernelFact.None.INSTANCE, Type.INT, POS);
    }
}
