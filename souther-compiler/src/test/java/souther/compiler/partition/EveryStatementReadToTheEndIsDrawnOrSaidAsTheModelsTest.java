package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The partition takes every statement a condition makes that was read to the end — draws its
 * lines — or says it divides nothing in a word about the model, and never in a word about what this
 * compiler did not get.
 *
 * <p>The partition's half of what every reader of a statement owes
 * ({@link EveryPropositionIsTakenOrMeetsTheEdgeOfAReadersWordsTest} holds the other readers to
 * it). It reads lines off the constructs a body writes, so a statement is handed to it as a
 * condition written to state it, and what it said is read off every reading of the walk: what each
 * place a construct names is left with, and what the fork around it is left stating. A word of the
 * family that says a reading stopped ({@link BlockReason.RuleReadingStopped}) about a statement
 * read to the end would be this reader's shortfall passed off as the statement's.
 *
 * <p>The kinds are taken from the sealed hierarchy, every kind met anywhere inside a sample, so a
 * kind of statement added without a condition stating it here is a failure. All but one: what a
 * condition states on one of several applications ({@link Proposition.OnAnApplication}) is no
 * statement this reader is handed, because a comparison inside a closure applied to values written
 * out is read on each application it is handed ({@code Cutting#onEachApplication}), and what it
 * states on each is one of the others.
 */
class EveryStatementReadToTheEndIsDrawnOrSaidAsTheModelsTest {

    private static final String DECLARATIONS = """
            module demo

            data A
            data B
            data Kind = A | B
            data Held = { o: Int? }
            data In = { n: Int, m: Int, b: Bool, s: String, h: Held, k: Kind, xs: List<Int>,
                        key: String, keys: List<String> }
            """;

    /** One condition for each way a statement can come out, each read to the end but the last. */
    private static Map<String, String> samples() {
        Map<String, String> out = new LinkedHashMap<>();
        out.put("always", "List.isEmpty([1, 2])");
        out.put("a relation of numbers", "i.n > 5");
        out.put("a place on an order", "i.s < \"M\"");
        out.put("a truth", "i.b");
        out.put("a case", "match i.k with | A -> true | B -> false");
        out.put("a value being there",
                "match Option.map(x -> x + 1, i.h.o) with | Some v -> true | None -> false");
        out.put("some element being a value", "List.contains(i.key, i.keys)");
        out.put("both", "i.n > 5 && i.b");
        out.put("either", "i.n > 5 || i.b");
        out.put("both, in one check", "List.length(if i.b then i.xs else []) >= 1");
        out.put("some element", "List.any(x -> x > 0, i.xs)");
        out.put("joined over values written out", "List.any(x -> x > 5, [i.n, i.m])");
        out.put("unread", "String.isEmpty(String.trim(i.s))");
        return out;
    }

    @Test
    void everyKindOfStatementHasACondition() {
        Set<Class<?>> met = new LinkedHashSet<>();
        samples().values().forEach(condition -> kindsIn(walked(condition).stated(), met));
        Set<Class<?>> missing =
                new LinkedHashSet<>(Arrays.asList(Proposition.class.getPermittedSubclasses()));
        missing.removeAll(met);
        missing.remove(Proposition.OnAnApplication.class);
        assertEquals(Set.of(), missing, "a kind of statement no condition here states");
    }

    @Test
    void aStatementReadToTheEndIsDrawnOrSaidInTheModelsWords() {
        samples().forEach((name, condition) -> {
            Walked walked = walked(condition);
            if (Proposition.leavesSomethingUnread(walked.stated())) {
                return;
            }
            for (BlockReason.RuleWithoutLineReason why : walked.said()) {
                assertInstanceOf(BlockReason.ReadToEndWithoutLine.class, why,
                        () -> name + " was read to the end: " + why);
            }
            assertEquals(List.of(), walked.leftToTheFork(),
                    () -> name + " was read to the end, and leaves its fork nothing to state");
        });
    }

    /** The control: a statement with a part nobody read is said to have stopped, somewhere. */
    @Test
    void aStatementWithAPartNobodyReadIsSaidToHaveStopped() {
        Walked walked = walked(samples().get("unread"));
        assertTrue(Proposition.leavesSomethingUnread(walked.stated()));
        assertFalse(walked.said().stream().noneMatch(BlockReason.RuleReadingStopped.class::isInstance)
                        && walked.leftToTheFork().isEmpty(),
                () -> "the part nobody read is said: " + walked);
    }

    private static void kindsIn(Proposition stated, Set<Class<?>> into) {
        into.add(stated.getClass());
        switch (stated) {
            case Proposition.All all -> all.parts().forEach(each -> kindsIn(each, into));
            case Proposition.Any any -> any.parts().forEach(each -> kindsIn(each, into));
            case Proposition.Some some -> kindsIn(some.ofTheElement(), into);
            case Proposition.OnAnApplication each -> each.each().forEach(one -> kindsIn(one, into));
            case Proposition.Always _, Proposition.Compared _, Proposition.Truth _,
                 Proposition.InCases _, Proposition.Present _, Proposition.SameValue _,
                 Proposition.Unread _ -> { }
        }
    }

    /**
     * What the fork stated, what each reading of the walk left at the places it names, and what
     * the fork is left stating.
     */
    private record Walked(Proposition stated, List<BlockReason.RuleWithoutLineReason> said,
                          List<ComparisonReadings.Atom> leftToTheFork) {}

    private static Walked walked(String condition) {
        Compilation compilation = Compilation.ofSource(DECLARATIONS + """

                behavior f : (i: In) -> Int
                let f (i) =
                    if (%s) then 1 else 0
                """.formatted(condition), "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), () -> "compiles: " + condition);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("f");
        InputReading read = inputs.reading(rules);
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        Core.If fork = assertInstanceOf(Core.If.class, Core.withoutStanding(analysis.core()));
        Proposition stated =
                Pullback.ofATruth(fork.cond(), reads, read, Optional.empty()).proposition();
        ComparisonReadings walk = ComparisonReadings.of("f", analysis, read, reads, reads,
                WhatAnAnswerTakesUp.of(read));
        List<BlockReason.RuleWithoutLineReason> said = new ArrayList<>();
        for (ComparisonReadings.Reading each : walk.comparisons()) {
            if (each.standing() instanceof BoundaryPolicy.Standing.Admitted(var assessment)) {
                assessment.whatEachPlaceIsLeftWith().forEach(left -> said.add(left.why()));
            }
        }
        return new Walked(stated, said, walk.forks().stream()
                .flatMap(each -> each.leftHere().stream()).toList());
    }
}
