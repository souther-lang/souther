package souther.compiler.inputs;

import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.ProjectionEvidence;
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

    /**
     * Where this position stops once every rule reaching the value it sits in has been taken in.
     *
     * <p>Beside {@link #narrowedEnds} and not the same question. That one is what the value this
     * sits in projects onto it, which a newtype's own value has nobody to be projected onto it by;
     * this is where the position starts and stops, whatever placed the ends and whatever moved them
     * afterwards. A caller deciding where a line actually falls wants this, because a clause placing
     * an end is not a clause that read the ones written beside it.
     */
    NumericDomain.Bounds rangeLeft();

    /** Which declarations' clauses are holding the end on the side asked for. */
    List<TypeSymbol> narrowedBy(boolean lower);

    /** Whether the rules of the value this position sits in contradict, so that no value of it
     *  exists to have positions at all. */
    boolean nothingExists();

    /**
     * How much of what the rules say the bounds of the value this position sits in are able to
     * state.
     *
     * <p>Asked of the whole value and not of this position, because that is what it is about: a rule
     * the bounds cannot express is a way the value can be refused wherever in it the rule is
     * written, so an edge at one of its positions is only as certain as the projection of all of
     * them.
     *
     * <p>Not whether a rule was answered, which is the wider question and is not this one:
     * {@code invariant nonzero = value /= 0} is read whole by the reading that turns clauses into
     * sets of values, and the edge at 0 is a row nobody can write all the same
     * ({@link souther.compiler.check.RuleAccounting} answers the other one).
     */
    ProjectionEvidence projection();

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

    /**
     * The same, of a case named by the declaration it is.
     *
     * <p>What a measure counting a sum's cases has in hand is the declaration, and what the reading
     * holds is a distinction it made from that declaration. Asked here so that the two meet by
     * identity: a caller rebuilding the distinction to look it up would have to know what the
     * reading knew when it made one, and would find nothing on the day that changed.
     */
    Admits admissionOf(TypeSymbol leaf);

    /**
     * How much of what the rules say about this position's values one reading took in.
     *
     * <p>That reading's account of itself, and nothing else. Nothing downstream decides anything
     * from it: the reading that turns clauses into sets of values has no word for a range, so it is
     * short of the rules at every numeric position an invariant bounds while two other readings
     * have those rules whole — and a measure written off this said a model had gone unread on the
     * strength of a fact about this compiler (issue #842). What a report is about is
     * {@link #unansweredQuestions()}.
     *
     * <p>Kept because the two are different answers and saying so is what stops them being merged
     * again: a position can carry a partial reading here and no question standing there, and a test
     * that could not state the pair could not hold the difference.
     */
    AdmissibleSet.Completeness completeness();

    /**
     * The questions the rules written about this position raise that nothing answered, each naming
     * the rule that raised it.
     *
     * <p>Not {@link #completeness()}. That is one reading's account of itself, and a reading being
     * short of a position's rules says nothing about whether the rules went unread: the reading
     * that turns a clause into a set of values has no word for a range, so it is short at every
     * numeric position an invariant bounds — while the reading that turns the same clause into
     * where the values stop had it whole. Read as the model's completeness, that is a rule reported
     * unread two lines above the boundary drawn from it (issue #842).
     *
     * <p>Empty where every rule about the position was taken in by something, whichever reading
     * that was. A reader deciding whether the numbers beside this position rest on a complete
     * reading of the model wants this and not a reading's own account.
     */
    List<StandingQuestion> unansweredQuestions();

    /**
     * Whether the walk never reached the rules written about this position.
     *
     * <p>Beside {@link #unansweredQuestions()} and not among them. A rule nothing took in is a rule
     * this compiler saw and made nothing of; here nothing was seen, so there is no rule to name and
     * no question to raise — and an empty list of questions says every rule was accounted for,
     * which is the opposite (issue #791).
     */
    boolean rulesNotReached();

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

    /**
     * The rules written about this position that the reading of ends could not turn into one.
     *
     * <p>Whichever value they are written on: a clause of this position's own type and a clause of
     * the value it sits in are two ways of saying where its values stop, and both come from the one
     * reading that draws lines from clauses.
     *
     * <p>Beside whatever the position is otherwise left with and not folded into it. A position
     * carries more than one statement, so an end read at it says nothing about the rule beside it —
     * kept as what the position was left with if nothing divided it, a bound on a field's own type
     * answered for the record's clause about the same field, and the clause was dropped in silence
     * (issue #868).
     */
    List<UnreadRule> unreadRules();

    /**
     * Whether the values at this position are read from a product this reading cannot show the
     * rules admit.
     *
     * <p>Beside {@link #valuesUnread()} and answering a different question. That one says what
     * stopped the reading; this one is true where nothing stopped it — every rule arrived and every
     * rule was taken in, and what is held is one set per position standing for a relation the two
     * of them cannot state. Read off {@link #completeness()} rather than carried, since it is the
     * same fact said in the vocabulary a caller here already has.
     */
    default boolean valuesNotSeparated() {
        return completeness() instanceof AdmissibleSet.Completeness.Wider wider
                && wider.why().contains(new AdmissibleSet.Widening.AlternativesNotSeparated());
    }

    /** Whether the position is made of positions, and what it is left with if nothing answers for
     *  it. */
    StructuralInspection structure();

}
