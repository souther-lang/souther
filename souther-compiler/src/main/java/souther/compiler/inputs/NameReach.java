package souther.compiler.inputs;

import java.util.ArrayList;
import java.util.List;

/**
 * Where a name written at one position stands, wherever that is not the position of the same name
 * one step down.
 *
 * <p>A field of a record is at the position under it, and nothing here says so. What needs saying is
 * the one place a name and a position part company: the fields a sum's cases all spread are readable
 * on a value of the sum, so a rule may name one of them at the sum — and a value there is of one
 * case, so what a row writes at that name is written under a case. The name is at the sum; the
 * positions are under each of its cases; and this is what the walk observed of the two.
 *
 * <p><b>Observed and not derived.</b> Every crossing here was recorded as the walk produced the
 * position it names, so a case the reading declined to walk and a field deeper than the reading goes
 * leave no crossing rather than a crossing to a position nobody made. What follows from a crossing
 * being absent is a question for whoever asks — there is no answer here that means "nowhere".
 *
 * <p><b>Structure and not a verdict.</b> These are facts about what stands where. Whether a rule
 * that names one of these positions was filed at it, refused, or left unresolved is settled against
 * these facts and is not one of them; read as an answer about a rule, a branch the reading never
 * owed would be a rule somebody failed to file.
 */
public record NameReach(List<Crossing> crossings, List<BranchNotEntered> branchesNotEntered,
                        List<NotStanding> notStanding) {

    public NameReach {
        crossings = List.copyOf(crossings);
        branchesNotEntered = List.copyOf(branchesNotEntered);
        notStanding = List.copyOf(notStanding);
    }

    /**
     * One name at one position standing at another, because the value there turned out to be a case
     * that spreads the declaration the name comes from.
     *
     * @param at      the sum's position, where the name is written
     * @param field   the name, which is a field every case of the sum spreads
     * @param branch  which case the value turned out to be, for a reader that has to say what a row
     *                at {@link #to} has to satisfy before it is anywhere
     * @param to      the position that name stands at once the value is that case
     */
    public record Crossing(TermPath at, String field, Refinement branch, TermPath to) {

        public Crossing {
            if (at == null || field == null || branch == null || to == null) {
                throw new IllegalArgumentException(
                        "a name stands somewhere, under something, and is called something");
            }
        }
    }

    /**
     * A case of a sum the reading did not go down, and so put no positions under.
     *
     * <p>Kept beside the crossings because the two are one observation of one sum: a name that
     * crosses into three of four cases crossed into three because the fourth was not walked, and a
     * reader with the crossings alone would have to work out from somewhere else whether the fourth
     * was refused or was never there.
     *
     * @param why which of the two it was, as the reading answered it. A reader saying what became of
     *            a name at this case reads it here rather than concluding one from the case having
     *            no positions — the two are different things to tell an author, and an absence is
     *            neither of them
     */
    public record BranchNotEntered(TermPath at, Refinement branch, NotEntered why) {

        public BranchNotEntered {
            if (at == null || branch == null || why == null) {
                throw new IllegalArgumentException(
                        "a case not entered is a case of some sum, and was not entered for a reason");
            }
        }
    }

    /**
     * Why the reading did not go down a case.
     *
     * <p>Two, and the two are the whole of it: these are the reasons the walk turns back at a
     * branch, and a third would be a third place it turns back at. How far down the reading goes is
     * not one of them — a case is entered whatever the depth, and what stops at a depth is the
     * product under it, which leaves a name with no position rather than a case with no reading.
     */
    public sealed interface NotEntered {

        /**
         * Naming the case builds it, so there is nothing under it to read.
         *
         * <p>A fact about the case and not about any rule. Nothing is missing here and nobody is
         * owed anything: a name has nowhere to stand under a case that holds nothing.
         */
        record NothingStandsUnderIt() implements NotEntered {}

        /**
         * The rules leave no value of this case, so nothing under it is owed.
         *
         * <p>What a rule naming a shared field asks of this case is asked of a case no row can
         * write. Read as a name that failed to reach somewhere, it would be a shortfall; it is the
         * reading holding to what it already said about the case.
         */
        record TheRulesLeaveNothingAtIt() implements NotEntered {}
    }

    /**
     * A case the reading went down that put no position at one of the shared names, and what the
     * reading of that case was left with.
     *
     * <p>Where the reading stops is observed under the case and not at the sum. A sum is read
     * whatever the depth — its cases are its own answer, not something below it — so a sum asked why
     * a shared name stands nowhere has nothing to say, and a reader taking its silence for an answer
     * would report that the model puts no such field there. What stopped is the product under the
     * case, and it says so where it is.
     */
    public record NotStanding(TermPath at, String field, Refinement branch,
                              BlockReason.AboutThePosition why) {

        public NotStanding {
            if (at == null || field == null || branch == null || why == null) {
                throw new IllegalArgumentException(
                        "a name that stands nowhere under a case does so for a reason the reading "
                                + "of that case gave");
            }
        }
    }

    /** Nothing observed: an input with no sum whose cases share a spread. */
    public static final NameReach NONE = new NameReach(List.of(), List.of(), List.of());

    /**
     * The positions {@code field}, written at {@code at}, stands at across the cases — empty where
     * that name does not cross a sum there.
     *
     * <p>Empty is the answer for every ordinary name, so it says only that nothing crosses here. A
     * caller wanting to know where an ordinary name stands asks what is one step down.
     *
     * <p>In the order the walk met the cases, which is the order the cases are declared in — so that
     * what a reader files, reports and counts is in the order the model is written.
     */
    public List<TermPath> across(TermPath at, String field) {
        List<TermPath> out = new ArrayList<>();
        for (Crossing each : crossings) {
            if (each.at().equals(at) && each.field().equals(field)) {
                out.add(each.to());
            }
        }
        return List.copyOf(out);
    }

    /**
     * Why {@code field}, written at {@code at}, stands nowhere under the cases the reading went
     * down — empty where it stands under all of them, or where nothing crosses here at all.
     *
     * <p>One per case that put no position there, because each of them is a place the name would
     * have stood and the readings need not have stopped alike.
     */
    public List<NotStanding> notStanding(TermPath at, String field) {
        List<NotStanding> out = new ArrayList<>();
        for (NotStanding each : notStanding) {
            if (each.at().equals(at) && each.field().equals(field)) {
                out.add(each);
            }
        }
        return List.copyOf(out);
    }

    /** What a walk writes its observations into. */
    static final class Observed {

        private final List<Crossing> crossings = new ArrayList<>();
        private final List<BranchNotEntered> notEntered = new ArrayList<>();
        private final List<NotStanding> notStanding = new ArrayList<>();

        /** Say that {@code field}, written at the sum standing at {@code at}, stands at {@code to}
         *  once the value there is the case {@code branch} names. */
        void crosses(TermPath at, String field, Refinement branch, TermPath to) {
            crossings.add(new Crossing(at, field, branch, to));
        }

        /** Say that the reading did not go down this case of the sum standing at {@code at}, and
         *  which of the two reasons it was. */
        void didNotEnter(TermPath at, Refinement branch, NotEntered why) {
            notEntered.add(new BranchNotEntered(at, branch, why));
        }

        /** Say that {@code field} stands nowhere under this case, and what the reading of the case
         *  was left with where it stopped. */
        void doesNotStand(TermPath at, String field, Refinement branch,
                          BlockReason.AboutThePosition why) {
            notStanding.add(new NotStanding(at, field, branch, why));
        }

        NameReach reach() {
            return crossings.isEmpty() && notEntered.isEmpty() && notStanding.isEmpty() ? NONE
                    : new NameReach(crossings, notEntered, notStanding);
        }
    }
}
