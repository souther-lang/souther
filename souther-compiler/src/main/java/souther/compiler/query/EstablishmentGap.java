package souther.compiler.query;

import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.publish.CanonicalSelection;
import souther.compiler.publish.PublicationOrders;

import java.util.Collection;

/**
 * What stopped this compiler establishing that a row can be written at a point.
 *
 * <p>Not a reason a row cannot be written. Every case here is a budget of this compiler's own
 * reached on the way to an answer, so what it licenses is that the question is open — and a reader
 * that turned one of these into a statement about the model would be reporting a policy as a
 * property of what somebody wrote.
 *
 * <p><b>Made where the establishing stopped, and never worked out afterwards.</b> The outcome a
 * search comes back with says that nothing came of it; which budget ran out is known only where it
 * ran out, and a reader recovering it from the outcome would be recovering it from something that
 * has already lost it — one reason a search comes back with is written wherever a search can stop,
 * by files that stop for nothing like each other. So a producer that stops hands this over, and one
 * that has nothing to hand over says so by there being no gap rather than by a gap nobody made.
 *
 * <p>Two cases, and what tells them apart is how far this compiler had got when it stopped. An
 * observation is of a value that exists and did not come back whole; a composing is of a value that
 * was never built. They leave the same question open and they are different work to close: one
 * takes keeping more of what is built, the other takes building more of what the rules leave.
 *
 * <p>What each of them holds is a {@link CanonicalSelection}, made where the gap is. A producer
 * hands over the reasons it met, in whatever order it met them, and what comes out is the order
 * they are published in — so nothing downstream has an order to decide, and nothing upstream has
 * one to keep.
 */
public sealed interface EstablishmentGap {

    /**
     * An observation of the value did not come back whole, so where it stands could not be read.
     *
     * <p>The value was built and the module's own decoders took it. What did not happen is the
     * reading back, and {@link Incompleteness.Code} is what says whether a limit shortened the
     * observation or nothing could be made of the value at all.
     */
    record Observation(CanonicalSelection<Incompleteness.Code> causes) implements EstablishmentGap {

        public Observation {
            if (causes == null || causes.isEmpty()) {
                throw new IllegalArgumentException(
                        "an observation that stopped something says what stopped it");
            }
        }

        /** The gap the codes an observation met are, in the order a document says them. */
        public static Observation of(Collection<Incompleteness.Code> causes) {
            return new Observation(PublicationOrders.OBSERVATION_CODES.keep(causes));
        }
    }

    /**
     * A figure of this compiler's is why no value composed for the point settles it.
     *
     * <p><b>Not that the figure is why nothing was composed.</b> Where a search ran over a plan
     * short of the point, raising the figure may well leave every candidate refused as before —
     * what the figure took away is not the row but the standing of the answer, which is about less
     * than the point had. Written the other way, a reader is told a figure caused an emptiness it
     * may have had nothing to do with.
     *
     * <p>Made where the figure was reached and carried out, never worked out afterwards. What a
     * search comes back with is a word, and two of this compiler's budgets come back with the same
     * word while one of them is written wherever a walk stops for any reason at all — so a reader
     * recovering a budget from that word would be recovering one that may never have been reached.
     * Some of the figures written here come back with no word at all.
     *
     * <p><b>Only where nothing was composed.</b> A budget that cut an offering short after a value
     * was built took nothing away from the point: the value is there, and what was lost is the rest
     * of an offer. Such a budget travels on what was built and not here, because a gap here is read
     * as the point having been left open by this compiler rather than by the model.
     *
     * <p>Which covers each way that happens. A figure may end the search before it had tried what
     * it held; a figure may leave the search running over less than the point had; and a figure may
     * leave nothing for a search to run over at all. The first comes back with the budgets' own
     * word, the second with a word of its own, and the third with a word saying no search was made
     * — and in every one of them what is written here is that the question is open on a figure
     * somebody could raise.
     *
     * <p>As many figures as were reached, because no two of them are the same piece of work.
     * Ranked, the one a reader was told about would be whichever was met first.
     */
    record Composition(CanonicalSelection<CompositionBudget> budgets) implements EstablishmentGap {

        public Composition {
            if (budgets == null || budgets.isEmpty()) {
                throw new IllegalArgumentException(
                        "a point this compiler left open says which figure left it open");
            }
        }

        /** The gap the budgets a search met are, in the order a document says them. */
        public static Composition of(Collection<CompositionBudget> budgets) {
            return new Composition(PublicationOrders.COMPOSITION_BUDGETS.keep(budgets));
        }
    }
}
