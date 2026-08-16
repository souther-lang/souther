package souther.compiler.inputs;

import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.TypeView;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.values.AdmissibleSet;

import java.util.List;

/**
 * One position of a behavior's input, read once.
 *
 * <p>What every measure means by "what can arrive here". The cases a signature is owed, the classes
 * a position divides into, the arms a row is owed and the claims a body makes about a case are four
 * questions with one answer behind them, and four derivations of that answer are four chances to
 * disagree — which is how a report came to ask for a row at a case its own rules refuse.
 *
 * <p><b>Settled questions only.</b> What is published here is what was decided, not what it was
 * decided from: the reading itself stays inside this package. Handed the readings, each caller
 * would interpret them again, and a fifth derivation is what this exists to stop.
 *
 * <p>Reached through {@link InputDomain} and nowhere else. There is no way to write one of these
 * down, which is the whole of what keeps the answer single: a caller cannot assemble a position
 * out of a claim a body made, and a widening cannot be applied twice because it is applied where
 * the position is made.
 */
public sealed interface Position permits ReadPosition {

    /** Where the position sits, which is how a rule written about it and a row walked to it meet. */
    TermPath path();

    /** The position's type as the signature wrote it. */
    Type type();

    /** The same, read through the names it is written under — what a value of it is, and what a row
     *  writes it as. */
    TypeView view();

    /** Which number this position is measured at: what it holds, or what its rules take of it. */
    NumericTerm term();

    /** What every rule reaching the position leaves its numbers, or null where nothing bounds them.
     *  Not where it is divided: a cap the record alone imposes stops the values without drawing a
     *  line through them. */
    NumericDomain.Bounds numericDomain();

    /** Where the position's own type says its values stop, with the declarations that said so. */
    DeclaredBounds.Bounds ownEnds();

    /** What the value the position sits in projects onto it, or null where it projects nothing. */
    NumericDomain.Bounds narrowedEnds();

    /** Which declarations' clauses are holding the end on the side asked for. */
    List<TypeSymbol> narrowedBy(boolean lower);

    /** Whether the rules of the value this position sits in contradict, so that no value of it
     *  exists to have positions at all. */
    boolean nothingExists();

    /**
     * Whether every rule of the value this position sits in was read.
     *
     * <p>Asked of the whole value and not of this position, because that is what it is about: a
     * rule this compiler could not read is a way the value can be refused wherever in it the rule
     * is written, so an edge at one of its positions is only as certain as the reading of all of
     * them.
     */
    boolean everyRuleOfTheValueWasRead();

    /** What crossing the position's distinctions with the rules came to, as the reading found it. */
    ReadingResult reading();

    /** What rows are owed here, which is the reading with this compiler's own widenings applied. */
    ObligationDomain obligations();

    /** The distinctions rows are owed, which is {@link #obligations()} read for its cases. */
    default List<Case> obligationCases() {
        return obligations().cases();
    }

    /**
     * What the declarations say about one distinction standing here.
     *
     * <p>Answered from the reading and from the widening together, so that a distinction present
     * only because the reading was set aside is never read as one the rules admit. A distinction
     * this position does not have at all is unsettled rather than refused: nothing was read about
     * it, and the two are different answers.
     */
    Admits admissionOf(Case one);

    /** How much of what the rules say about this position's values was read. */
    AdmissibleSet.Completeness completeness();

    /**
     * What stopped the reading of which values this position may hold, or null where nothing did.
     *
     * <p>{@link #completeness()} said in the vocabulary a report is projected from. Kept apart from
     * whatever left a <em>bound</em> unread: a rule stating where the values stop and a rule naming
     * which values there are are read by different readers of the same clause, and only the second
     * is what decides whether an absence of classes may be reported as the model stating no
     * division.
     */
    BlockReason valuesUnread();

    /** The rules written about this position that the reading could not turn into an end. */
    List<UnreadRule> unreadRules();

    /** Whether the position is made of positions, and what it is left with if nothing answers for
     *  it. */
    StructuralInspection structure();
}
