package souther.compiler.reading;

import org.junit.jupiter.api.Test;

import souther.compiler.WhatWasCompiled;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.partition.MeaningsOfABodyReading;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fork in a copy of one of the language's operations is entered where what its condition states
 * can come out that way, read by the rules a model's conditions are read by.
 *
 * <p>The model wrote the call and not the fork, so the fork has no site of the model; what its
 * condition states is still what the operation's body says at the call, its parameters standing
 * for what the call handed. {@code Bool.not(i.n > 5)} is copied as a fork on what it was handed,
 * and that fork's condition states that {@code i.n} is past five — a statement over the input,
 * and not a node a reader of the tree would have to take apart for itself.
 */
class AForkInACopyOfTheLibraryIsReadForWhatItStatesTest {

    private static final String MODEL = """
            module demo

            data In = { n: Int }

            behavior f : (i: In) -> Int
            let f (i) = if Bool.not(i.n > 5) then 1 else 0
            """;

    @Test
    void theConditionOfACopiedForkIsAStatementOverTheInput() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model compiles");
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("f");
        InputReading read = inputs.reading(rules);
        InputReads reads = InputReads.ofParameters(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.NONE, inputs.dependencies());

        Found found = copiedFork(checked.behaviorBodies().get("f"), reads);
        assertNotNull(found, "the run of f holds a copy of Bool.not with a fork in it");
        Proposition stated =
                MeaningsOfABodyReading.ofACopiedCondition(found.fork().cond(), found.at(), read);
        assertTrue(Proposition.stopsIn(stated).isEmpty(), () -> "read to the end: " + stated);
        assertTrue(stated.key().contains("i.n"), () -> "over the input: " + stated);
    }

    /** The one place a copied fork's condition is asked for what it states. */
    @Test
    void onlyTheWaysThroughARunAskIt() {
        assertEquals(Set.of("souther.compiler.reading.NumberWays"),
                WhatWasCompiled.callersOf(MeaningsOfABodyReading.class, "ofACopiedCondition"));
    }

    private record Found(Core.If fork, InputReads at) {}

    /** The first fork in a copy of {@code Bool.not} in {@code e}, with the reading of what stands
     *  bound around it. */
    private static Found copiedFork(Core e, InputReads at) {
        if (e instanceof Core.If fork
                && fork.place().occurrence().lineage() instanceof OccurrenceLineage.Expansion copy
                && copy.expanded().equals(ValueName.Stdlib.operation("Bool", "not"))) {
            return new Found(fork, at);
        }
        if (e instanceof Core.LetIn let) {
            Found inValue = copiedFork(let.value(), at);
            return inValue != null ? inValue
                    : copiedFork(let.body(), at.and(let.binder(), let.value()));
        }
        Found[] found = {null};
        Core.forEachChild(e, child -> {
            if (found[0] == null) {
                found[0] = copiedFork(child, at);
            }
        });
        return found[0];
    }
}
