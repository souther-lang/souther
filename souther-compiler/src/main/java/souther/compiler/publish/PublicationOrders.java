package souther.compiler.publish;

import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.ReadingGap;
import souther.compiler.query.EstablishmentGap;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.ObligationDisposition;

import java.util.ArrayList;
import java.util.List;

/**
 * The order a kind of reason is published in, for the kinds that arrive without one.
 *
 * <p>Not every kind. Where a plurality comes with the order the model has — the reasons a question
 * stands are the parts of the rule that raised it, and a document promises that order — nothing
 * here has anything to decide, and an order written for such a kind would answer by a precedence
 * nothing in the model decides ({@link SourceOrdered}). What is written here is for the kinds that
 * cross saying which of them hold and nothing more.
 *
 * <p>Of those, one kind, one order. A kind said in two places — an observation's code is said of a
 * reading that stopped short and again of a value nothing could read back — has one order all the
 * same, or the two lines of one block would put the same pair of reasons in two orders and nothing
 * would say which was meant.
 *
 * <p>Written here rather than read off how the constants are declared. A declaration is arranged
 * for whoever reads the code, and moving one is a change nobody expects to see in a document; read
 * off {@code values()} or off an {@code EnumSet}, it is one, and every consumer of the report has
 * to be compared against the last run to find it.
 *
 * <p>None of these orders is a rank. What they are for is that a report comes out the same twice,
 * and what a reader does with two reasons is do both.
 */
public final class PublicationOrders {

    private PublicationOrders() {}

    /**
     * What an observation met instead of a value, from what was nearest an answer to what never
     * started.
     *
     * <p>A value in hand that could not be read comes first, then the two about the row that would
     * have held one, then what the row was to be run against, then the run itself, and last the two
     * that say nothing was observed at all. So the reasons a wider budget would change are said
     * before the ones nothing about this compiler's own limits would.
     */
    private static final List<Incompleteness.Code> OBSERVATION_CODES_IN_ORDER = List.of(
            Incompleteness.Code.VALUE_UNREADABLE,
            Incompleteness.Code.VALUE_TRUNCATED,
            Incompleteness.Code.ROW_UNDECIDED,
            Incompleteness.Code.ROW_EVALUATION_LIMIT_REACHED,
            Incompleteness.Code.ANSWERER_NOT_ESTABLISHED,
            Incompleteness.Code.LINKAGE_FAILED,
            Incompleteness.Code.OBSERVATION_ABSENT,
            Incompleteness.Code.INSTRUMENTATION_ABSENT);

    /** What an observation met, wherever a document says one. */
    public static final CanonicalSelection.Order<Incompleteness.Code> OBSERVATION_CODES =
            CanonicalSelection.Order.overValues(OBSERVATION_CODES_IN_ORDER);

    /**
     * What a reading of a number met instead of one.
     *
     * <p>Composed from the order above and not written again. A reading that met an observation's
     * code is that code, so the two orders agreeing is not something to keep in step — there is one
     * order, and this is it with the one reason that is no observation's put after them. A walk
     * that reached no value is last for the same reason the codes are in the order they are: it is
     * the furthest from an answer.
     */
    public static final CanonicalSelection.Order<ReadingGap> READING_GAPS =
            CanonicalSelection.Order.overValues(everyReadingGap());

    private static List<ReadingGap> everyReadingGap() {
        List<ReadingGap> out = new ArrayList<>();
        for (Incompleteness.Code code : OBSERVATION_CODES_IN_ORDER) {
            out.add(ReadingGap.of(code));
        }
        out.add(ReadingGap.NO_VALUE);
        return out;
    }

    /**
     * What this compiler declined to do, from what bounds one value to what bounds a whole search.
     *
     * <p>Nearest the value a reader wanted first. What one proposed value is worth building comes
     * before what one total is offered as, and both before what the search spends over everything
     * it tries — so the figure they would raise to get the value in front of them is said before
     * the ones that bound the work around it. The plan's depth is last, as the only one that says
     * how far this compiler looks before it has anything at all.
     */
    public static final CanonicalSelection.Order<CompositionBudget> COMPOSITION_BUDGETS =
            CanonicalSelection.Order.overValues(List.of(
                    CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS,
                    CompositionBudget.CHARACTERS_A_PROPOSAL_HOLDS,
                    CompositionBudget.PAIRINGS_BUILT_AT_ONCE,
                    CompositionBudget.ELEMENTS_A_TOTAL_IS_SPREAD_OVER,
                    CompositionBudget.SHAPES_OF_A_TOTAL_OFFERED,
                    CompositionBudget.DECOMPOSITIONS_OF_A_TOTAL_OFFERED,
                    CompositionBudget.VALUES_OF_AN_UNBOUNDED_PROGRESSION_TRIED,
                    CompositionBudget.PLACES_A_PAIR_IS_TRIED_AT,
                    CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT,
                    CompositionBudget.LEVELS_A_SIDE_IS_ASKED_AT,
                    CompositionBudget.ASSIGNMENTS_A_SEARCH_COMPOSES,
                    CompositionBudget.TIMES_THE_RULES_ARE_ASKED_AGAIN,
                    CompositionBudget.STEPS_A_SEARCH_MAY_TAKE,
                    CompositionBudget.DEPTH_A_CONSTRUCTION_PLAN_DESCENDS));

    /**
     * What stopped this compiler showing a row can be written, by how far it had got.
     *
     * <p>A value that was built and did not come back whole is nearer an answer than one that was
     * never built, which is the order the reasons inside each of them are in as well.
     *
     * <p>The arms and not what they hold. Which observation codes an arm says, and which budgets,
     * are the orders above; said again here they would be a second order over kinds that have one.
     */
    public static final CanonicalSelection.Order<EstablishmentGap> ESTABLISHMENT_GAPS =
            CanonicalSelection.Order.overFamilies(List.<Class<? extends EstablishmentGap>>of(
                    EstablishmentGap.Observation.class,
                    EstablishmentGap.Composition.class));

    /**
     * What is open about an obligation nobody can decide.
     *
     * <p>What a reader does about the two differs — the first is answered by reading more of what
     * is written and the second is not work an author can do — and the first is said first because
     * it is the one they can act on.
     *
     * <p>The questions and not the answers. Each of the two is open for more than one reason, and a
     * place per reason would say twice what the sentence says once.
     */
    public static final CanonicalSelection.Order<ObligationDisposition.Uncertainty> OPEN_QUESTIONS =
            CanonicalSelection.Order.overFamilies(
                    List.<Class<? extends ObligationDisposition.Uncertainty>>of(
                            ObligationDisposition.Uncertainty.WhetherARowIsThere.class,
                            ObligationDisposition.Uncertainty.WhetherARowCanBeWritten.class));

    /**
     * What a document says one measurement went without.
     *
     * <p>Two vocabularies in one array ({@link WeakeningVocabulary}), and one order over the pair.
     * The observation codes come first and in the order they are said in everywhere else, then the
     * words this document has of its own — a value that was read and did not come back whole is
     * nearer an answer than a reading that never happened, which is the principle the codes are
     * already in the order of.
     *
     * <p>The words of this document's own are in the order the things they are about are met: what
     * a row came back with, then what was read of the model, then what the rules left, then what a
     * proof or an arm came to.
     */
    public static final CanonicalSelection.Order<WeakeningVocabulary> WEAKENING_WORDS =
            CanonicalSelection.Order.overValues(everyWeakeningWord());

    private static List<WeakeningVocabulary> everyWeakeningWord() {
        List<WeakeningVocabulary> out = new ArrayList<>();
        for (Incompleteness.Code code : OBSERVATION_CODES_IN_ORDER) {
            out.add(new WeakeningVocabulary.AnObservationCode(code));
        }
        for (WeakeningWord word : List.of(
                WeakeningWord.OUTPUT_CASES_UNREADABLE,
                WeakeningWord.INPUT_CASES_UNREADABLE,
                WeakeningWord.BORDER_VALUE_UNREADABLE,
                WeakeningWord.BORDER_VALUE_ABSENT,
                WeakeningWord.BODIES_NOT_ELABORATED,
                WeakeningWord.BEHAVIOR_INPUT_NOT_READ,
                WeakeningWord.BEHAVIOR_BOUNDARY_NOT_DERIVED,
                WeakeningWord.RULE_UNREAD,
                WeakeningWord.POSITION_NOT_READ,
                WeakeningWord.RULES_NOT_REACHED,
                WeakeningWord.QUESTION_UNANSWERED,
                WeakeningWord.PAIR_SPACE_TRUNCATED,
                WeakeningWord.PROOF_CONTRADICTED,
                WeakeningWord.ARMS_UNSETTLED)) {
            out.add(new WeakeningVocabulary.AWordOfThisDocuments(word));
        }
        return out;
    }

    /**
     * What has shown a row can be written at a point.
     *
     * <p>The one ground that is about the model first, then the two that are about this run, and of
     * those the one a row already answers before the one a value was built for. So a reader sees
     * what stands whatever this run did before what this run happened to reach.
     */
    public static final CanonicalSelection.Order<ItemAssessment.WritabilityEvidence.Ground>
            WRITABILITY_GROUNDS = CanonicalSelection.Order.overValues(List.of(
                    ItemAssessment.WritabilityEvidence.Ground.THE_RULES_PROVE_IT,
                    ItemAssessment.WritabilityEvidence.Ground.A_ROW_IS_AT_IT,
                    ItemAssessment.WritabilityEvidence.Ground.A_VALUE_WAS_BUILT));
}
