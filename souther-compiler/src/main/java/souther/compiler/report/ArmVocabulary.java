package souther.compiler.report;

import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.OutcomeName;
import souther.compiler.coverage.SourceOutcome;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.stream.Collectors;
import java.util.Locale;

/**
 * What the reports written in one language call one way through a construct.
 *
 * <p>Here rather than beside the measurement. What a way through a construct <em>is</em> is a
 * construct and a {@link SourceOutcome}, and both of those are the same however they are asked
 * about; what to call one is a question only somebody with a reader in front of them has, and there
 * are two such readers with different needs — a table and a document that join on a short word, and
 * a diagnostic that says a phrase in whatever language it was asked in. The second is the catalog's.
 *
 * <p>Written off {@link souther.compiler.coverage.OutcomeName}, which is the pair already settled, so
 * a construct or an outcome added to the language reaches this as a name it has to be given a word
 * for rather than as a case that falls through.
 */
public final class ArmVocabulary {

    /**
     * The short word a table prints and a document writes under {@code label}.
     *
     * <p>One function for both, because the document's {@code subject} joins a finding to the entry
     * in {@code branch.obligations} that names the same arm: spelled twice, the two would join to
     * nothing the day one of them was reworded.
     */
    public static String label(CoverageSites.Site arm) {
        return label(arm.construct(), arm.outcome());
    }

    /**
     * The same word for an outcome of a construct, where no site of it is in hand.
     *
     * <p>An arm is a construct and an outcome whether or not a run through it is recorded, and a
     * sibling an arm is rewritten as is often one nothing records. Both readers come here, so an
     * arm a rewrite names and the same arm a branch line names are one word.
     */
    public static String label(SourceConstruct construct, SourceOutcome outcome) {
        return switch (outcome) {
            case SourceOutcome.Matched(List<TypeSymbol> cases) -> "case " + namesOf(cases);
            // The word the author put the departure under, and the clause where they named one. The
            // name of this outcome is `departure`, which says what happened rather than what is
            // written there; a reader of a table is looking at the file.
            case SourceOutcome.Failed(SourceOutcome.FailedBy.Construction(var clause)) ->
                    clause.map(c -> "else " + c).orElse("else");
            case SourceOutcome.Compared(var op) -> op.toString();
            case SourceOutcome.Held _, SourceOutcome.Failed _ ->
                    OutcomeName.of(construct, outcome).name().toLowerCase(Locale.ROOT);
        };
    }

    private static String namesOf(List<TypeSymbol> cases) {
        return cases.stream().map(TypeSymbol::name)
                .collect(Collectors.joining(" | "));
    }

    private ArmVocabulary() {}
}
