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

        /**
         * Where {@code path} stands once the value at the sum is this case, or null where this
         * crossing is not above it.
         *
         * <p>{@link #to} is this asked of the name itself. A path below that name answers with the
         * same step put in, because what a clause relates under a shared name are positions under
         * the case for the same reason the name is.
         *
         * <p>Asked of the crossing the walk recorded rather than worked out again from the path: the
         * step that says which case the value turned out to be is written in one place, and a second
         * one would put a name under a case by a rule of its own.
         */
        public TermPath standingUnderTheCase(TermPath path) {
            return SharedNames.under(path, at, branch, field);
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
     * Where a name written at a sum stands once the value is one of its cases, and what a row has
     * to be for it to stand there.
     *
     * <p><b>The condition travels with the position.</b> A row is one value, so every name of one
     * sum is written under one case: two of these chosen apart would ask for a value that is two
     * cases at once. Held as a position alone, that constraint would be stated nowhere and each
     * name would be sent wherever it could go — so what a reader merges is
     * {@link Requirements#merge}, which already refuses two answers at one position, rather than a
     * rule of its own about which branches go together.
     *
     * @param assuming what the value at the sum has to have turned out to be
     * @param position where the name stands under it, which is what a row rebuilds
     */
    public record CaseStanding(Requirements assuming, TermPath position) {

        public CaseStanding {
            if (assuming == null || position == null) {
                throw new IllegalArgumentException(
                        "a name standing under a case stands somewhere, and only where the row is"
                                + " that case");
            }
        }
    }

    /**
     * Where the values a path names stand, which is the path itself except where a name crosses.
     *
     * <p>Structure and not a verdict, like everything else here. What follows for a reader is the
     * reader's — one narrowing a search by has nothing to narrow by at a name that crosses, and one
     * choosing where to write has the cases to choose between.
     */
    public sealed interface Standing {

        /**
         * Nothing crosses here: the values a row writes stand where the path says.
         *
         * <p>The answer for every ordinary name, and for a path this reading never reached. That
         * those two are one answer is what makes this structure rather than a verdict: whether the
         * reading answered for the path is what the reading's own positions say, and this says only
         * that no name was seen to cross.
         */
        record AtThePathItself() implements Standing {}

        /**
         * Under the cases of a sum whose every case the walk went down put the name somewhere.
         *
         * <p>Every case the walk opened, which is what makes the list a choice a writer may make: a
         * row written as any one of them holds a value at the name.
         */
        record UnderTheCases(List<CaseStanding> standings) implements Standing {

            public UnderTheCases {
                standings = List.copyOf(standings);
                if (standings.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a name that stands under the cases stands under at least one of them");
                }
            }
        }

        /**
         * A name that crosses, where the reading of some case stopped before putting it anywhere.
         *
         * <p>Both halves, because a writer may not act on either alone. The cases that do hold the
         * name are a choice; the ones whose reading stopped are positions whose rules were never
         * read, and a row written as one of those would be offered at a position nothing answered
         * for. Collapsed into one word, whichever half a reader looked at would decide the other's
         * answer.
         */
        record CasesIncomplete(List<CaseStanding> standings, List<NotStanding> stopped)
                implements Standing {

            public CasesIncomplete {
                standings = List.copyOf(standings);
                stopped = List.copyOf(stopped);
                if (stopped.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a name the cases are read alike at is UnderTheCases, and one no case"
                                    + " crosses is AtThePathItself");
                }
            }
        }
    }

    /**
     * Where the values {@code path} names stand.
     *
     * <p>The one place a path is sorted into these, because every reader that acts on the difference
     * has to act on the same sorting. A search narrowing by sets and a writer choosing where to put
     * a value ask for different grains of the answer and not for different answers — sorted where
     * each of them spends it, the two would part over the first case whose reading stopped.
     *
     * <p>Asked of the crossings the walk recorded and of the cases it went down without putting the
     * name anywhere. The cases it never went down say nothing: naming a case that holds nothing
     * builds it, and a case the rules leave no value of is one no row writes — neither is a name
     * this reading fell short of.
     *
     * <p><b>One crossing at a time, and the answer says so.</b> A name under two sums is moved by
     * the outer one before the inner one can see it, so a position answered with here can itself be
     * a name that crosses — a caller acting on one asks this of what it got back, and a position
     * that crosses again is one this has not finished moving. Run to a fixed point instead, the
     * answer would be a case of every sum on the way and the choices would multiply inside a type
     * that records what a walk saw.
     */
    public Standing standingOf(TermPath path) {
        List<CaseStanding> standings = null;
        List<NotStanding> stopped = null;
        for (Crossing crossing : crossings) {
            TermPath under = crossing.standingUnderTheCase(path);
            if (under != null) {
                if (standings == null) {
                    standings = new ArrayList<>();
                }
                standings.add(new CaseStanding(
                        Requirements.NONE.and(crossing.at(), crossing.branch()), under));
            }
        }
        for (NotStanding each : notStanding) {
            // The sum first, which is a prefix of the steps and answers no for everything this
            // reading met elsewhere. The name below it is a path to build, and building one to
            // find out it was never the right sum is what a reading with no crossings pays.
            if (path.isAtOrUnder(each.at()) && path.isAtOrUnder(each.at().then(each.field()))) {
                if (stopped == null) {
                    stopped = new ArrayList<>();
                }
                stopped.add(each);
            }
        }
        if (stopped != null) {
            return new Standing.CasesIncomplete(
                    standings == null ? List.of() : standings, stopped);
        }
        return standings == null ? NOWHERE_ELSE : new Standing.UnderTheCases(standings);
    }

    /** The answer for every name no case carries, which is most of them and holds nothing. */
    private static final Standing NOWHERE_ELSE = new Standing.AtThePathItself();

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
        private final List<NotStanding> notStanding = new ArrayList<>();
        /**
         * What became of every case of every sum the walk met, by the sum it belongs to.
         *
         * <p>One recording and two readings of it. Why a name did not cross a case and whether that
         * case has a value are different questions with one answer behind them — the walk decides
         * both at the step it turns back at a branch — so what is written down is what became of the
         * case, and {@link #reach()} is a view of it rather than a second account.
         */
        private final java.util.SequencedMap<TermPath,
                java.util.SequencedMap<Refinement, CaseOutcome>> cases =
                new java.util.LinkedHashMap<>();

        /** Say that {@code field}, written at the sum standing at {@code at}, stands at {@code to}
         *  once the value there is the case {@code branch} names. */
        void crosses(TermPath at, String field, Refinement branch, TermPath to) {
            crossings.add(new Crossing(at, field, branch, to));
        }

        /** Say what became of this case of the sum standing at {@code at}. */
        void became(TermPath at, Refinement branch, CaseOutcome outcome) {
            cases.computeIfAbsent(at, of -> new java.util.LinkedHashMap<>()).put(branch, outcome);
        }

        /** Every sum the walk met, with what became of each of its cases. */
        List<CasesRead> cases() {
            List<CasesRead> out = new ArrayList<>();
            cases.forEach((at, outcomes) -> out.add(new CasesRead(at, outcomes)));
            return List.copyOf(out);
        }

        /** Say that {@code field} stands nowhere under this case, and what the reading of the case
         *  was left with where it stopped. */
        void doesNotStand(TermPath at, String field, Refinement branch,
                          BlockReason.AboutThePosition why) {
            notStanding.add(new NotStanding(at, field, branch, why));
        }

        NameReach reach() {
            List<BranchNotEntered> notEntered = new ArrayList<>();
            // The two the model answers for, read off the one recording. A case the walk opened has
            // its answer under it, and a case the walk never went down is this reading's shortfall
            // and not a case a name failed to reach — read as one, a name would be reported as
            // standing nowhere because the walk stopped before it got there.
            cases.forEach((at, outcomes) -> outcomes.forEach((branch, outcome) -> {
                switch (outcome) {
                    case CaseOutcome.StandsAlone _ -> notEntered.add(new BranchNotEntered(at,
                            branch, new NotEntered.NothingStandsUnderIt()));
                    case CaseOutcome.RefusedByTheRules _ -> notEntered.add(new BranchNotEntered(at,
                            branch, new NotEntered.TheRulesLeaveNothingAtIt()));
                    case CaseOutcome.Opened _, CaseOutcome.NotWalked _ -> { }
                }
            }));
            return crossings.isEmpty() && notEntered.isEmpty() && notStanding.isEmpty() ? NONE
                    : new NameReach(crossings, notEntered, notStanding);
        }
    }
}
