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
import souther.compiler.types.BinOp;
import souther.compiler.types.ConstructOccurrence;
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
 *
 * <p>Each argument is a sum of two numbers, so that working one out can stop the run: a run works
 * every argument out before the call, and a fold that answered from the case reached without one
 * of them — {@code Int.clamp} answers its low end below it without its high end — answers where
 * the program stops.
 */
class AFoldOfAnOperationDefinedByCasesAnswersWhatTheProgramAnswersTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    /** Each end of an {@code Int}, nought, and either side of it. */
    private static final List<Long> NUMBERS = List.of(Long.MIN_VALUE, -1L, 0L, 1L,
            Long.MAX_VALUE);

    /** An argument worked out as its number and what is added to it. */
    private record Argument(long number, long added) {

        static Argument of(long number) {
            return new Argument(number, 0);
        }

        /** An argument whose working out stops the run: past the greatest {@code Int}. */
        static final Argument STOPPING = new Argument(Long.MAX_VALUE, 1);

        Core written() {
            return new Core.Binary(BinOp.ADD, new Core.Int(number, Type.INT, POS),
                    new Core.Int(added, Type.INT, POS), Core.BinaryReading.AS_THEY_STAND,
                    ConstructOccurrence.unwritten(), Type.INT, POS);
        }
    }

    private static final List<String> PLACES = List.of("a", "b", "c");

    private static final List<String> ADDED = List.of("x", "y", "z");

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

                data In = { a: Int, b: Int, c: Int, x: Int, y: Int, z: Int }
                data Out = Int
                """);
        for (int at = 0; at < operations.size(); at++) {
            ValueName.Stdlib.Operation operation = operations.get(at);
            List<String> args = new ArrayList<>();
            for (int place = 0; place < arityOf(operation); place++) {
                args.add("i." + PLACES.get(place) + " + i." + ADDED.get(place));
            }
            model.append("""

                    behavior b%d : (i: In) -> Out
                    let b%d (i) = Out { value = %s.%s(%s) }
                    """.formatted(at, at, operation.alias(), operation.name(),
                    String.join(", ", args)));
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
            for (List<Argument> args : everyChoiceOf(arityOf(operation))) {
                Map<String, Object> in = new LinkedHashMap<>();
                for (int place = 0; place < PLACES.size(); place++) {
                    Argument one = place < args.size() ? args.get(place) : Argument.of(0);
                    in.put(PLACES.get(place), one.number());
                    in.put(ADDED.get(place), one.added());
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
        Stdlib.Entry entry = DefaultStdlib.get().entry(operation);
        return entry.signature().result() == Type.INT
                && entry.signature().params().stream().allMatch(Type.INT::equals);
    }

    private static int arityOf(ValueName.Stdlib.Operation operation) {
        return DefaultStdlib.get().entry(operation).signature().params().size();
    }

    /** Every list of {@code arity} of {@link #NUMBERS}, and each such list with one of its
     *  arguments one whose working out stops the run. */
    private static List<List<Argument>> everyChoiceOf(int arity) {
        List<List<Argument>> out = new ArrayList<>(List.of(List.of()));
        for (int place = 0; place < arity; place++) {
            List<List<Argument>> next = new ArrayList<>();
            for (List<Argument> sofar : out) {
                for (Long number : NUMBERS) {
                    List<Argument> one = new ArrayList<>(sofar);
                    one.add(Argument.of(number));
                    next.add(one);
                }
            }
            out = next;
        }
        List<List<Argument>> stopping = new ArrayList<>();
        for (List<Argument> each : out) {
            for (int place = 0; place < arity; place++) {
                List<Argument> one = new ArrayList<>(each);
                one.set(place, Argument.STOPPING);
                stopping.add(one);
            }
        }
        out.addAll(stopping);
        return out;
    }

    /** A call to {@code operation} over {@code args}. */
    private static Core.PreservedCall callTo(ValueName.Stdlib.Operation operation,
                                             List<Argument> args) {
        List<Core> written = new ArrayList<>();
        args.forEach(each -> written.add(each.written()));
        return new Core.PreservedCall(KeptCalls.declared(operation), written,
                new Core.KeptCallPlace(new FixtureReferenceOrigin(0),
                        new ApplicationOrigin.ComposedFixture(), OccurrenceLineage.ORIGINAL),
                Core.KernelFact.None.INSTANCE, Type.INT, POS);
    }
}
