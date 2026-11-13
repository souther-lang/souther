package souther.compiler.query;

import souther.compiler.ACompiledModel;
import souther.compiler.check.AssumedContract;
import souther.compiler.check.StatedContract;
import souther.compiler.conformance.ConformanceCorpus;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.ValueName;
import souther.test.ClosedWorldContract;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a caller depends on of a contract is what it states, over every contract the conformance
 * corpus writes.
 *
 * <p>A contract is read into terms, and a term carries where it was written and the ordinal its
 * module numbered it with. Neither is anything a caller reads — it substitutes its own arguments in
 * and reads what the terms say — so two readings of one declaration that differ only in where the
 * file put it are the same dependency. {@link StatedContract#assumptions()} is where that is
 * decided, and {@link souther.compiler.check.TermMeaning} is what it decides with.
 *
 * <p>This asks it of {@link Bodies.Assumptions}, over what the corpus states. It does not ask it of
 * every kind of term: the corpus states one {@code ensures}, which reaches a handful of the node
 * kinds a reading is projected over, and a kind whose place was compared in a shape this never
 * meets would pass here. That is {@code EveryTermIsReadForWhatItSaysTest}, which asks the same
 * question of one node kind at a time, and
 * {@code EveryKindOfTermACorpusWritesIsReadForWhatItSaysTest}, which reports the kinds nothing
 * reaches. All three are wanted: one holds the projection, one holds what a model writes, and this
 * holds what the query graph does with it.
 *
 * <p>Moving the whole file is the edit: every position in it changes, and every construct is
 * numbered after the ones the blank lines did not add, so a place surviving anywhere in a contract
 * shows up here as an inequality.
 */
@ClosedWorldContract
class WhatACallerAssumesIsWhatWasStatedNotWhereItWasWrittenTest {

    /** Every behavior that states something, in every module of every corpus. */
    private static Map<ValueName.Behavior, AssumedContract> assumed(Compilation c) {
        Map<ValueName.Behavior, AssumedContract> out = new LinkedHashMap<>();
        for (String module : c.modules()) {
            Map<String, StatedContract> stated =
                    c.db().ask(new Bodies.StatedContracts(module)).value();
            if (stated == null) {
                continue;
            }
            for (String behavior : stated.keySet()) {
                ValueName.Behavior named = new ValueName.Behavior(module, behavior);
                Answer<AssumedContract> answer = c.db().ask(new Bodies.Assumptions(named));
                if (answer.present()) {
                    out.put(named, answer.value());
                }
            }
        }
        return out;
    }

    /** The corpora written to be refused, and what each is refused for. */
    private static final Map<String, List<String>> CORPUS_REFUSALS =
            Map.of("booking", List.of("E2010", "E1013"));

    private static Compilation compiled(ConformanceCorpus corpus, String before) {
        Map<String, String> byId = new LinkedHashMap<>();
        for (int i = 0; i < corpus.sources().size(); i++) {
            byId.put(corpus.files().get(i), before + corpus.sources().get(i));
        }
        Compilation compilation = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        return ACompiledModel.refusedWith(
                CORPUS_REFUSALS.getOrDefault(corpus.name(), List.of()), compilation);
    }

    @Test
    void movingEveryLineOfEveryCorpusChangesNoContractACallerDependsOn() {
        List<String> checked = new ArrayList<>();
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            Map<ValueName.Behavior, AssumedContract> where =
                    assumed(compiled(corpus, ""));
            Map<ValueName.Behavior, AssumedContract> moved =
                    assumed(compiled(corpus, "\n\n\n"));

            assertEquals(where.keySet(), moved.keySet(),
                    corpus.name() + " states the same contracts wherever its lines are");
            assertEquals(where, moved,
                    corpus.name() + " states the same thing three lines further down");
            if (!where.isEmpty()) {
                checked.add(corpus.name() + ":" + where.size());
            }
        }
        assertTrue(!checked.isEmpty(),
                "some corpus writes a contract, or this asks nothing: " + checked);
    }
}
