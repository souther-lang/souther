package souther.compiler;

import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.DeclaredRows;
import souther.compiler.query.GenerationScope;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * The rows one behavior is offered at the lines its values are held to, for a test that asks about
 * one behavior.
 *
 * <p>Two authorities and one question. A line the behavior's own rules drew is its own and is in its
 * filling; a line an {@code invariant} drew is the declaration's, is offered once over every
 * behavior carrying the type, and is resolved for the module (issue #1076). What a person reading
 * the block beside one behavior sees is both, and that is what this puts back together.
 *
 * <p>Asked of the module and then narrowed, which is the order that matters. Resolved per behavior,
 * every carrier would compose its own row for one line and the count this exists to hold would be
 * the count before the change.
 */
public final class OfferedAtTheLines {

    /** What is offered at one behavior's lines, in the block's own order: its own first, and the
     *  lines a declaration is owed that this behavior's reading composed after them. */
    public static Generator.GenerationResult of(Compilation compilation, String module,
                                                String behavior) {
        Map<String, Adequacy.Filling> all = Adequacy.generatedOf(compilation.db(), module);
        Adequacy.Filling filling = all == null ? null : all.get(behavior);
        Generator.GenerationResult own = filling == null
                ? Generator.GenerationResult.NONE : filling.boundaries();
        DeclaredRows declared = Adequacy.generatedForDeclarationsOf(compilation.db(), module,
                new GenerationScope.Module());
        List<Generator.GeneratedRow> rows = souther.compiler.report.GeneratedRows.atTheLines(
                own.rows(), declared.rowsByCarrier().get(behavior));
        List<Generator.UnresolvedCombination> unresolved = new ArrayList<>(own.unresolved());
        declared.unmet().forEach(unmet -> {
            switch (unmet) {
                case DeclaredRows.Unmet.TheLineCannotBeWritten(var _, var _, var proving) ->
                        proving.forEach(at -> unresolved.add(at.why()));
                case DeclaredRows.Unmet.WhatTheReadingsCameTo(var _, var _, var came) ->
                        came.forEach(at -> unresolved.add(at.why()));
                case DeclaredRows.Unmet.NothingWasSearched(var _, var _) -> { }
            }
        });
        return new Generator.GenerationResult(rows, unresolved, own.reasons());
    }

    private OfferedAtTheLines() {}
}
