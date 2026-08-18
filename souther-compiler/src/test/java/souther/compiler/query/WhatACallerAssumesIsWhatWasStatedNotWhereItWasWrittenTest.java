package souther.compiler.query;

import souther.compiler.conformance.ConformanceCorpus;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.ValueName;

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
 * file put it are the same dependency. {@link Bodies.Assumed} is where that is decided, and
 * {@link souther.compiler.core.Core#withoutItsPlace} is what it decides with.
 *
 * <p>Asked of the corpus rather than of a term written here. The rewrite is a case per kind of
 * node, and a case that kept a place would go on passing a test written against the shapes whoever
 * wrote the rewrite had in mind. The corpus is written to reach every construct the language
 * declares, so what it compiles is the wide reading.
 *
 * <p>Moving the whole file is the edit: every position in it changes, and every construct is
 * numbered after the ones the blank lines did not add, so a place surviving anywhere in a contract
 * shows up here as an inequality.
 */
class WhatACallerAssumesIsWhatWasStatedNotWhereItWasWrittenTest {

    /** Every behavior that states something, in every module of every corpus. */
    private static Map<ValueName.Behavior, Bodies.Assumed> assumed(Compilation c) {
        Map<ValueName.Behavior, Bodies.Assumed> out = new LinkedHashMap<>();
        for (String module : c.modules()) {
            Map<String, souther.compiler.check.StatedContract> stated =
                    c.db().ask(new Bodies.StatedContracts(module)).value();
            if (stated == null) {
                continue;
            }
            for (String behavior : stated.keySet()) {
                ValueName.Behavior named = new ValueName.Behavior(module, behavior);
                Answer<Bodies.Assumed> answer = c.db().ask(new Bodies.Stated(named));
                if (answer.present()) {
                    out.put(named, answer.value());
                }
            }
        }
        return out;
    }

    private static Compilation compiled(List<String> files, List<String> sources, String before) {
        Map<String, String> byId = new LinkedHashMap<>();
        for (int i = 0; i < sources.size(); i++) {
            byId.put(files.get(i), before + sources.get(i));
        }
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        return c;
    }

    @Test
    void movingEveryLineOfEveryCorpusChangesNoContractACallerDependsOn() {
        List<String> checked = new ArrayList<>();
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            Map<ValueName.Behavior, Bodies.Assumed> where =
                    assumed(compiled(corpus.files(), corpus.sources(), ""));
            Map<ValueName.Behavior, Bodies.Assumed> moved =
                    assumed(compiled(corpus.files(), corpus.sources(), "\n\n\n"));

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
