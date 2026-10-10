package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.WhatTheLibraryComputes;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.proof.AppliedClosures;
import souther.compiler.proof.Slot;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.ClosurePositions;
import souther.compiler.semantics.Combinator;
import souther.compiler.semantics.ElementLineage;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every axiom about a kernel holds of what the kernel computes, over values chosen at the edges it
 * turns on.
 *
 * <p>A kernel has no body to prove anything of, so what is stated of one is an axiom, and a proof
 * that takes it is as sound as it is. These are the axioms the proofs of the library's written
 * operations take beside a kernel's laws (which {@code EveryLawHoldsOfWhatTheLibraryComputesTest}
 * runs): what its answer comes to beside what others answer, the containers it is no smaller than,
 * the one value it puts in, what it lists, what it builds its answer from, and how far it goes
 * applying its closure. Each is written from the axiom itself and run
 * ({@link WhatTheLibraryComputes}); how far a closure is applied is run through a closure that
 * stops the call at the one element it is marked to stop on, so whether the call stops is whether
 * that element was handed to it.
 */
class EveryAxiomAboutAKernelHoldsOfWhatItComputesTest {

    private static final LawSubject<Slot> ANSWER = new LawSubject.Argument<>(new Slot.Answer());

    private static final LawSubject<Slot> ANY = new LawSubject.Argument<>(new Slot.Every(0));

    @Test
    void everyAxiomStatedOfAKernelHoldsOfWhatItAnswers() throws Exception {
        Stdlib stdlib = DefaultStdlib.get();
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        List<WhatTheLibraryComputes.Statement> statements = new ArrayList<>();
        for (ValueName.Stdlib.Operation operation : stdlib.entries().keySet()) {
            if (stdlib.intrinsicOf(operation) == null) {
                continue;   // what is stated of a written operation is proved of its body
            }
            for (LawProposition<Slot> related : facts.relationsOf(operation)) {
                statements.add(new WhatTheLibraryComputes.Statement(operation, "related",
                        related));
            }
            for (DeclaredArgument container : facts.resultIsNoSmallerThan(operation)) {
                statements.add(new WhatTheLibraryComputes.Statement(operation,
                        "no smaller than " + container.position(), compared(Rel.GE, 0,
                                size(ANSWER), size(at(container.position())).negate())));
            }
            if (facts.putsAValueIn(operation) instanceof BoundOperationFact.PutsAValueIn puts) {
                statements.add(new WhatTheLibraryComputes.Statement(operation, "puts a value in",
                        putsIn(puts.value().position(), puts.into().position())));
            }
            if (Combinators.listing(stdlib, facts, operation)
                    instanceof AppliedClosures.Listing listing) {
                statements.add(new WhatTheLibraryComputes.Statement(operation, "lists",
                        lists(listing)));
            }
            if (facts.buildsItsResultFrom(operation) instanceof BuiltFrom<DeclaredArgument> built) {
                statements.add(new WhatTheLibraryComputes.Statement(operation, "builds",
                        builds(operation, built)));
            }
        }
        WhatTheLibraryComputes.Held held = WhatTheLibraryComputes.run(statements);
        assertEquals(List.of(), held.broken());
        assertEquals(List.of(), held.neverAnswered(), "an axiom held to no call that answered");
    }

    @Test
    void everyKernelAppliesItsClosureAsFarAsItIsDeclaredTo() throws Exception {
        Stdlib stdlib = DefaultStdlib.get();
        Map<ValueName.Stdlib.Operation, Combinator> kernels = Combinators.kernelsIn(stdlib);
        StringBuilder source = new StringBuilder("module demo\n\ndata N = { n: Int }\n");
        Map<ValueName.Stdlib.Operation, Type> containers = new LinkedHashMap<>();
        int index = 0;
        for (var each : kernels.entrySet()) {
            source.append('\n').append(stopping(index++, each.getKey(), each.getValue(), stdlib,
                    containers));
        }
        WhatTheLibraryComputes.Program program =
                new WhatTheLibraryComputes.Program("demo", source.toString());
        List<String> wrong = new ArrayList<>();
        index = 0;
        for (var each : kernels.entrySet()) {
            int at = index++;
            List<List<Long>> held = containers.get(each.getKey()) instanceof Type.OptionOf
                    ? List.of(List.of(), List.of(2L), List.of(0L))
                    : List.of(List.of(), List.of(2L), List.of(0L, 2L), List.of(2L, 0L),
                            List.of(-1L, 0L, 2L), List.of(1L, 2L, 1L));
            for (List<Long> elements : held) {
                for (long mark : List.of(0L, 1L, 2L, 5L)) {
                    Map<String, Object> input = new HashMap<>();
                    input.put("m", mark);
                    input.put("s", "");
                    input.put("xs", containers.get(each.getKey()) instanceof Type.OptionOf
                            ? (elements.isEmpty() ? null : elements.getFirst()) : elements);
                    boolean stopped;
                    try {
                        program.answer("kernel" + at, "K" + at, "N", input);
                        stopped = false;
                    } catch (RuntimeException stopping) {
                        if (!WhatTheLibraryComputes.stopsOnItsArguments(stopping)) {
                            throw stopping;
                        }
                        stopped = true;
                    }
                    if (stopped != handed(each.getValue(), elements, mark)) {
                        wrong.add(each.getKey().qualified() + " " + each.getValue().applied()
                                + " over " + elements + (stopped ? " was" : " was not")
                                + " handed " + mark);
                    }
                }
            }
        }
        assertEquals(List.of(), wrong);
    }

    /**
     * Whether a closure a kernel applying it {@code rule.applied()} is handed {@code mark}, over a
     * container holding {@code elements} in that order, where it holds of what is above nought.
     */
    private static boolean handed(Combinator rule, List<Long> elements, long mark) {
        return switch (rule.applied()) {
            case TO_EVERY_ELEMENT -> elements.contains(mark);
            case UNTIL_ONE_HOLDS -> {
                for (long each : elements) {
                    if (each == mark) {
                        yield true;
                    }
                    if (each > 0) {
                        yield false;
                    }
                }
                yield false;
            }
            case UNTIL_ONE_FAILS -> {
                for (long each : elements) {
                    if (each == mark) {
                        yield true;
                    }
                    if (each <= 0) {
                        yield false;
                    }
                }
                yield false;
            }
            // Which one is not said, so a run that stops says nothing against it; one kernel
            // declared so is one this is to say how to run.
            case AT_MOST_ONE, TO_SOME -> throw new IllegalStateException(
                    "no run here says which elements a closure applied " + rule.applied()
                            + " is handed");
        };
    }

    /**
     * The behavior {@code kernel<index>}, calling {@code operation} with a closure that stops the
     * call on the element the input marks and holds of what is above nought otherwise, over the
     * container the input hands it. The container's type goes into {@code containers}.
     */
    private static String stopping(int index, ValueName.Stdlib.Operation operation,
                                   Combinator rule, Stdlib stdlib,
                                   Map<ValueName.Stdlib.Operation, Type> containers) {
        Stdlib.Signature declaration = stdlib.entry(operation).signature();
        List<Type> params = WhatTheLibraryComputes.instantiated(declaration.params(), declaration);
        Type answers = WhatTheLibraryComputes.instantiated(List.of(declaration.result()),
                declaration).getFirst();
        if (params.size() != 2 || rule.handsAKey()) {
            throw new IllegalStateException(operation + " takes more than a closure and what it"
                    + " is applied to, which no run here hands it");
        }
        Type container = params.get(rule.containerArg());
        containers.put(operation, container);
        Type.FnOf closure = (Type.FnOf) params.get(rule.closureArg());
        String stops = switch (closure.result()) {
            case Type.Prim prim when prim == Type.Prim.BOOL ->
                    "String.isEmpty(String.slice(0, 1, i.s))";
            case Type.Prim prim when prim == Type.Prim.INT ->
                    "String.length(String.slice(0, 1, i.s))";
            default -> throw new IllegalStateException("no closure answering "
                    + Type.show(closure.result()) + " is written here");
        };
        String otherwise = closure.result() == Type.Prim.BOOL ? "v > 0" : "v";
        List<String> args = new ArrayList<>(List.of("", ""));
        args.set(rule.closureArg(), "v -> if v == i.m then " + stops + " else " + otherwise);
        args.set(rule.containerArg(), "i.xs");
        String call = operation.qualified() + "(" + String.join(", ", args) + ")";
        String measured = switch (answers) {
            case Type.ListOf _ -> "List.length(" + call + ")";
            case Type.OptionOf _ -> "Option.withDefault(0, Option.map(y -> 1, " + call + "))";
            default -> throw new IllegalStateException("no measure of "
                    + Type.show(answers) + " is written here");
        };
        return "data K" + index + " = { m: Int, s: String, xs: " + Type.show(container)
                + " }\n\nbehavior kernel" + index + " : (i: K" + index
                + ") -> N constructs N\nlet kernel" + index + " (i) = N { n = " + measured
                + " }\n";
    }

    /** At most one element more than the container at {@code into}, each one of its or the value
     *  at {@code value}. */
    private static LawProposition<Slot> putsIn(int value, int into) {
        LawProposition<Slot> eachFromTheTwo = new LawProposition.SomeElement<>(new Slot.Answer(),
                new LawProposition.Any<>(List.of(
                        same(new LawSubject.ElementOf<>(new Slot.Answer()), argument(value)),
                        new LawProposition.SomeElement<>(new Slot.Place(into),
                                same(new LawSubject.ElementOf<>(new Slot.Place(into)),
                                        new LawSubject.ElementOf<>(new Slot.Answer())), true)))
                        .denied(), false);
        return new LawProposition.All<>(List.of(compared(Rel.LE, -1, size(ANSWER),
                size(at(into)).negate()), eachFromTheTwo));
    }

    /** What an answer listing {@code listing} of an argument holds of it: every element of the
     *  one in the other, as many of them, and none listed twice where none is. */
    private static LawProposition<Slot> lists(AppliedClosures.Listing listing) {
        return switch (listing) {
            case AppliedClosures.Listing.EveryElementOf(int argument, boolean eachDifferent) -> {
                // As many, every one of the argument's among them, and each of them one of the
                // argument's: so where the argument's are each different, so are they.
                List<LawProposition<Slot>> parts = new ArrayList<>(List.of(
                        compared(Rel.EQ, 0, size(ANSWER), size(at(argument)).negate()),
                        among(new Slot.Answer(), new Slot.Place(argument)),
                        among(new Slot.Place(argument), new Slot.Answer())));
                if (eachDifferent) {
                    parts.add(compared(Rel.LE, 0, howMany(new Slot.Answer()),
                            howMany(new Slot.Place(argument)).negate()));
                }
                yield new LawProposition.All<>(parts);
            }
            // An entry is a pair, which no statement here names, so what is run is that there are
            // as many as the map holds.
            case AppliedClosures.Listing.EveryEntryOf(int argument) ->
                    compared(Rel.EQ, 0, size(ANSWER), size(at(argument)).negate());
            case AppliedClosures.Listing.AtMostOneElementOf(int argument) ->
                    among(new Slot.Answer(), new Slot.Place(argument));
        };
    }

    /**
     * What an answer built as {@code built} holds of where it came from: no value more times than
     * the source holds it, or than the closure answers it of the source's elements — each element
     * a different one of the source's — and as many as {@code built} says.
     */
    private static LawProposition<Slot> builds(ValueName.Stdlib.Operation operation,
                                               BuiltFrom<DeclaredArgument> built) {
        if (built.outputs().size() != 1
                || !built.outputs().getFirst().at().equals(ElementLineage.ResultPath.elements())) {
            throw new IllegalStateException(operation + " builds more than one run of elements,"
                    + " which no run here checks");
        }
        ElementLineage.Source<DeclaredArgument> source;
        LawSubject<Slot> made;
        switch (built.outputs().getFirst().origin()) {
            case ElementLineage.SameAs<DeclaredArgument>(var from) -> {
                source = from;
                made = new LawSubject.ElementOf<>(new Slot.Place(from.argument().position()));
            }
            case ElementLineage.ClosureResult<DeclaredArgument>(var from) -> {
                source = from;
                ClosurePositions positions = Combinators.positionsOf(operation);
                made = new LawSubject.WhatTheClosureAnswers<>(
                        new Slot.Place(positions.closureArg()));
            }
            case ElementLineage.InsideClosureResult<DeclaredArgument> _,
                 ElementLineage.OneOf<DeclaredArgument> _ -> throw new IllegalStateException(
                    operation + " builds " + built + ", which no run here checks");
        }
        if (source.elements() != 1) {
            throw new IllegalStateException(operation + " builds from inside the elements of an"
                    + " argument, which no run here checks");
        }
        Slot from = new Slot.Place(source.argument().position());
        LawProposition<Slot> noMore = compared(Rel.LE, 0,
                count(new Slot.Answer(), new LawSubject.ElementOf<>(new Slot.Answer())),
                count(from, made).negate());
        LawProposition<Slot> asMany = switch (built.size()) {
            case SAME -> compared(Rel.EQ, 0, size(ANSWER), size(at(from)).negate());
            case AT_MOST -> compared(Rel.LE, 0, size(ANSWER), size(at(from)).negate());
        };
        return new LawProposition.All<>(List.of(noMore, asMany));
    }

    /** Every element of {@code each} is one {@code of} holds. */
    private static LawProposition<Slot> among(Slot each, Slot of) {
        return new LawProposition.SomeElement<>(each, new LawProposition.SomeElement<>(of,
                same(new LawSubject.ElementOf<>(of), new LawSubject.ElementOf<>(each)), true)
                .denied(), false);
    }

    /** How many elements of {@code container} {@code subject}, said of each, is any value. */
    private static LinearForm<LawNumber<Slot>> count(Slot container, LawSubject<Slot> subject) {
        return LinearForm.atom(new LawNumber.HowManyMeet<>(container, same(subject, ANY)));
    }

    /** How many elements of {@code container} are any value. */
    private static LinearForm<LawNumber<Slot>> howMany(Slot container) {
        return count(container, new LawSubject.ElementOf<>(container));
    }

    private static LawProposition<Slot> same(LawSubject<Slot> one, LawSubject<Slot> other) {
        return new LawProposition.Same<>(one, other, true);
    }

    private static LawSubject<Slot> argument(int position) {
        return new LawSubject.Argument<>(new Slot.Place(position));
    }

    private static LawSubject<Slot> at(int position) {
        return argument(position);
    }

    private static LawSubject<Slot> at(Slot slot) {
        return new LawSubject.Argument<>(slot);
    }

    private static LinearForm<LawNumber<Slot>> size(LawSubject<Slot> of) {
        return LinearForm.atom(new LawNumber.SizeOf<>(of));
    }

    /** {@code one} and {@code other} together, plus {@code constant}, standing as {@code rel}
     *  says to nought. */
    private static LawProposition<Slot> compared(Rel rel, long constant,
                                                 LinearForm<LawNumber<Slot>> one,
                                                 LinearForm<LawNumber<Slot>> other) {
        Map<LawNumber<Slot>, ExactRatio> coefs = new LinkedHashMap<>(one.coefs());
        other.coefs().forEach((number, by) -> {
            if (coefs.put(number, by) != null) {
                throw new IllegalStateException("one number twice in " + one + " and " + other);
            }
        });
        return new LawProposition.Compared<>(new LinearForm<>(ExactRatio.of(constant), coefs),
                rel);
    }
}
