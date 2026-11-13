package souther.compiler.meaning;

import souther.compiler.check.ClauseName;
import souther.compiler.inputs.InputReads;
import souther.compiler.types.AnApplicationOfACall;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.Predicate;
import java.util.function.Supplier;

/**
 * What each condition of one body states, filed under the construct of the model it is asked at.
 *
 * <p>Read once, off the representation where the language's operations stand, and looked up by a
 * reader walking the tree that runs: the two trees agree about which construct of the model a node
 * is one of ({@link ModelOccurrence}), and about nothing finer. One construct may be met at more
 * than one place in either tree — a helper's construct is copied wherever the helper is — and where
 * the copies here state different things the site is ambiguous and answers nothing, so no reader
 * takes one copy's statement for another's.
 *
 * <p>Two copies are compared by what they state and not by how it was derived. Two expansions of
 * one helper can reach one proposition by different rules, and that makes the site no less one
 * statement. How the first was derived is the one kept, and it is part of what this is equal by:
 * a reader explaining a fork from it would otherwise be handed an account a revision ago.
 *
 * <p>A site inside a closure read once for each application states, here, what it states on the
 * application a run meets it on ({@link Proposition.OnAnApplication}), which says what can come out
 * and not which application states what. What each application's reading of the body states is
 * kept beside it, filed by which application it is ({@link #onTheApplication}), for a reader that
 * knows which application it stands on. Each is filed as this is, a site met again on it compared
 * by what it states ({@link Filing#metAll}), so what an application states is the same question
 * as what a site states and is answered one way.
 *
 * @param stated    what is stated at each site read to one statement, and how — never a site
 *                  whose copies state different things, so nothing read off this is one of them
 * @param ambiguous the sites whose copies state different things
 * @param piecesAttempted the pieces of a string of the input that the body builds a newtype of,
 *                  in the order the walk met them
 * @param applications what the body of a closure read on each of its applications states on that
 *                  application, by which application it is
 *                  ({@link InputReads.Applications.Made#which})
 */
public record MeaningsOfABody(Map<Site, Meaning> stated, Set<Site> ambiguous,
                              Set<PieceDemand> piecesAttempted,
                              Map<AnApplicationOfACall, MeaningsOfABody> applications) {

    /** A body nothing was read of. */
    public static final MeaningsOfABody NONE =
            new MeaningsOfABody(Map.of(), Set.of(), Set.of(), Map.of());

    public MeaningsOfABody {
        stated = Map.copyOf(stated);
        ambiguous = Set.copyOf(ambiguous);
        piecesAttempted = Collections.unmodifiableSet(new LinkedHashSet<>(piecesAttempted));
        applications = Map.copyOf(applications);
        for (Site each : ambiguous) {
            if (stated.containsKey(each)) {
                throw new IllegalArgumentException(
                        "a site whose copies state different things states none of them: " + each);
            }
        }
    }

    /**
     * Which part of a construct is asked whether it holds: a truth the construct asks, or an arm of
     * a fork a run enters.
     */
    public sealed interface Part permits Part.Asked, Part.Arm {

        /** A truth a construct asks. */
        enum Asked implements Part {
            /** The condition a fork chooses its arm by. */
            CONDITION,
            /** The left operand of a short-circuit, which decides whether the right one runs. */
            LEFT,
            /** The construct itself, a comparison whose outcome a run records. */
            ITSELF
        }

        /**
         * An arm of a fork, which holds where a run enters it.
         *
         * <p>Named by what the source names it by, so that an arm is the same arm in every copy of
         * the fork and after an edit that moves another: a case of a {@code match} by where it is
         * written among the cases, and an arm of an attempt by the clause of the invariant it
         * answers.
         */
        sealed interface Arm extends Part {}

        /** The arm of a {@code match} written {@code arm}-th among its cases, from nought. */
        record OfACase(int arm) implements Arm {

            public OfACase {
                if (arm < 0) {
                    throw new IllegalArgumentException("a case is written somewhere among the cases");
                }
            }
        }

        /** The arm of an attempt taken where every clause of the invariant held and the value was
         *  built. */
        record Built() implements Arm {}

        /**
         * A departure of an attempt: the one answering the clause named {@code clause} — the first
         * clause not to hold — or, where empty, the one answering every failure no other departure
         * names.
         */
        record Departed(Optional<ClauseName> clause) implements Arm {

            public Departed {
                Objects.requireNonNull(clause, "a departure names a clause or names none");
            }
        }
    }

    /**
     * Where a truth is asked: a construct of the model, and which part of it.
     *
     * @param construct the construct the two readings of the body agree it is
     * @param part      which of its parts is the truth asked
     */
    public record Site(ModelOccurrence construct, Part part) {}

    /**
     * What a site states, and how that was derived.
     *
     * <p>Made by concluding the derivation and no other way ({@link Conclusion#meaningOf}), so what
     * is stated is always what the derivation beside it concludes. Two values alike in both are
     * equal.
     */
    public static final class Meaning {

        private final Proposition states;
        private final Derivation how;

        Meaning(Proposition states, Derivation how) {
            this.states = Objects.requireNonNull(states, "a site states something");
            this.how = Objects.requireNonNull(how, "what a site states was derived");
        }

        /** What holds where the truth asked there does. */
        public Proposition states() {
            return states;
        }

        /** The derivation it was concluded from. */
        public Derivation how() {
            return how;
        }

        /**
         * The rows on which a run stops in what this states ({@link Derivation.TheRunStopsHere}),
         * or null where none does: for each place the derivation stops a run at, the conditions of
         * the {@code if}s it is down an arm of.
         *
         * <p>Only what stands between the statement and the stop is a condition of it. Any other
         * step on the way is left out, so the rows are the rows the way to the stop admits and may
         * be more than the rows that reach it; a stop is dropped only where the conditions kept
         * rule every row out.
         */
        public Proposition whereARunStops() {
            List<Proposition> stops = new ArrayList<>();
            new Walk(step -> step instanceof Derivation.TheRunStopsHere, (step, down) -> {
                stops.add(down.all());
            }).down(how, Down.NO_ARM);
            return stops.isEmpty() ? null : Proposition.any(stops);
        }

        /**
         * Each relation a comparison was read as in what this states, with where it is read: the
         * conditions of the {@code if}s and the arms it is down, as {@link #whereARunStops} has
         * them, all holding. A relation read on no arm is read wherever the statement is. The
         * same relation read on two arms is said once for each.
         *
         * <p>What working the relation's comparison out does is worked out where it is read, and
         * nowhere else: a sum on one arm is no sum of a run that takes the other.
         */
        public List<ReadOnAnArm> relationsDownTheArms() {
            return relationsDownTheArmsOf(how);
        }

        /** The same, of {@code how}, a derivation a site's may be made of. */
        public static List<ReadOnAnArm> relationsDownTheArmsOf(Derivation how) {
            List<ReadOnAnArm> out = new ArrayList<>();
            new Walk(MeaningsOfABody.Meaning::isAComparisonRead, (step, down) -> {
                out.add(new ReadOnAnArm(((Derivation.AComparisonRead) step).relation(),
                        down.all()));
            }).down(how, Down.NO_ARM);
            return List.copyOf(out);
        }

        /**
         * The relations {@link #relationsDownTheArmsOf} has of {@code how}, without where each is
         * read: for a reader that asks only which relations were read on some arm, so that no
         * condition of an arm is worked out for it.
         */
        public static List<Relation> relationsReadIn(Derivation how) {
            List<Relation> out = new ArrayList<>();
            new Walk(MeaningsOfABody.Meaning::isAComparisonRead, (step, _) -> {
                out.add(((Derivation.AComparisonRead) step).relation());
            }).down(how, Down.NO_ARM);
            return List.copyOf(out);
        }

        private static boolean isAComparisonRead(Derivation step) {
            return step instanceof Derivation.AComparisonRead;
        }

        /**
         * A relation a comparison was read as, and where it is read.
         *
         * @param relation the relation
         * @param reached  where the arms it is down are taken
         */
        public record ReadOnAnArm(Relation relation, Proposition reached) {

            public ReadOnAnArm {
                Objects.requireNonNull(relation, "a relation read");
                Objects.requireNonNull(reached, "is read somewhere, if only nowhere");
            }
        }

        /**
         * Every step the walk wants below a step, each handed to {@code at} with the conditions of
         * the arms it is down.
         *
         * <p>A derivation is a graph where a name was used twice, so what is asked of a step is
         * asked once: whether a step wants anything below it, and whether a step has been handed
         * over at the arms it is down already. A step is down the arms of each way to it, which
         * differ by the conditions of the {@code if}s on the way, and each of those is said: the
         * same relation read on two arms is said once for each.
         */
        private static final class Walk {

            private final Predicate<Derivation> wanted;
            private final BiConsumer<Derivation, Down> at;
            private final Map<Derivation, Boolean> holdsOneWanted = new IdentityHashMap<>();
            private final Map<Derivation, Set<Down>> handedOver = new IdentityHashMap<>();

            Walk(Predicate<Derivation> wanted, BiConsumer<Derivation, Down> at) {
                this.wanted = wanted;
                this.at = at;
            }

            /** Whether {@code step} is wanted or has a wanted step below it. */
            private boolean holdsOneWanted(Derivation step) {
                Boolean known = holdsOneWanted.get(step);
                if (known != null) {
                    return known;
                }
                boolean holds = wanted.test(step);
                if (!holds && !(step instanceof Derivation.TheRunStopsHere)) {
                    for (Derivation each : WrittenLines.premisesOf(step)) {
                        if (holdsOneWanted(each)) {
                            holds = true;
                            break;
                        }
                    }
                }
                holdsOneWanted.put(step, holds);
                return holds;
            }

            void down(Derivation step, Down down) {
                if (!holdsOneWanted(step)
                        || !handedOver.computeIfAbsent(step, _ -> new HashSet<>()).add(down)) {
                    return;
                }
                if (wanted.test(step)) {
                    at.accept(step, down);
                }
                if (step instanceof Derivation.TheRunStopsHere) {
                    return;
                }
                if (step instanceof Derivation.IfThenElse(Derivation condition, Derivation then,
                                                          Derivation otherwise)) {
                    Later decides = new Later(() -> condition.concludes(Optional.empty()));
                    down(condition, down);
                    down(then, down.and(decides));
                    down(otherwise, down.and(() -> decides.get().denied()));
                    return;
                }
                // An arm is down where it selects the value and, for arms taken in order, no arm
                // before it does; what selects is worked out before any arm.
                switch (step) {
                    case Derivation.MatchArms(var arms) -> down(arms, true, down);
                    case Derivation.AnOperationsCases(var _, var cases) ->
                            down(cases, true, down);
                    case Derivation.ASizeInCases(var _, var cases) -> down(cases, true, down);
                    case Derivation.OneOfItsArms(var arms) -> down(arms, false, down);
                    default -> WrittenLines.premisesOf(step).forEach(each -> down(each, down));
                }
            }

            private void down(List<Derivation.MatchArms.Arm> arms, boolean inOrder, Down down) {
                List<Later> before = new ArrayList<>();
                for (Derivation.MatchArms.Arm arm : arms) {
                    Later selects = new Later(() -> arm.selects().concludes(Optional.empty()));
                    down(arm.selects(), down);
                    List<Later> earlier = List.copyOf(before);
                    Supplier<Proposition> reached = !inOrder ? selects
                            : () -> Derivation.taken(earlier.stream().map(Later::get).toList(),
                                    selects.get());
                    down(arm.states(), down.and(reached));
                    before.add(selects);
                }
            }
        }

        /**
         * The arms a step is down, outermost first. Where they are taken is worked out only for a
         * reader that asks, and once for all the steps down the same arms.
         */
        private static final class Down {

            static final Down NO_ARM = new Down(null, null);

            private final Down outer;
            private final Supplier<Proposition> arm;
            private Proposition all;

            private Down(Down outer, Supplier<Proposition> arm) {
                this.outer = outer;
                this.arm = arm;
            }

            Down and(Supplier<Proposition> taken) {
                return new Down(this, taken);
            }

            /** Every arm taken: what holds where a step down them is. */
            Proposition all() {
                if (all == null) {
                    List<Proposition> taken = new ArrayList<>();
                    for (Down each = this; each.arm != null; each = each.outer) {
                        taken.add(each.arm.get());
                    }
                    Collections.reverse(taken);
                    all = Proposition.all(taken);
                }
                return all;
            }
        }

        /** A condition of an arm, worked out the first time it is asked for. */
        private static final class Later implements Supplier<Proposition> {

            private Supplier<Proposition> work;
            private Proposition held;

            Later(Supplier<Proposition> work) {
                this.work = work;
            }

            @Override
            public Proposition get() {
                if (held == null) {
                    held = work.get();
                    work = null;
                }
                return held;
            }
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Meaning that && states.equals(that.states)
                    && how.equals(that.how);
        }

        @Override
        public int hashCode() {
            return Objects.hash(states, how);
        }

        @Override
        public String toString() {
            return "Meaning[states=" + states + ", how=" + how + "]";
        }
    }

    /**
     * What is stated at each site, filed as copies of it are met.
     *
     * <p>A site met again is compared by what the copy states: the same proposition derived another
     * way is the same statement and leaves the first derivation where it is, and another proposition
     * makes the site ambiguous, which it stays whatever is met there after.
     */
    public static final class Filing {

        private final Map<Site, Meaning> stated = new LinkedHashMap<>();
        private final Set<Site> ambiguous = new HashSet<>();
        private final Set<PieceDemand> piecesAttempted = new LinkedHashSet<>();
        private final Map<AnApplicationOfACall, Filing> applications = new LinkedHashMap<>();

        /** {@code demands}, met where a construction is attempted of the pieces of a string. */
        public void metAsPieces(List<PieceDemand> demands) {
            piecesAttempted.addAll(demands);
        }

        /**
         * {@code meaning}, met at {@code site}. Two copies of a site are read through the names
         * of their own copies, which is no difference in what the site states where the names of
         * one stand one to one for the names of the other; where they do not, the copies state
         * different things ({@link ReadThroughNames#sameUpToTheNames}).
         */
        public void met(Site site, Meaning meaning) {
            if (ambiguous.contains(site)) {
                return;
            }
            Meaning before = stated.putIfAbsent(site, meaning);
            if (before != null
                    && !ReadThroughNames.sameUpToTheNames(before.states(), meaning.states())) {
                ambiguousAt(site);
            }
        }

        /**
         * Everything {@code reading} filed, met as this filing meets what it reads itself: each
         * site it states as a copy met here, each site it found ambiguous as ambiguous here, the
         * pieces it attempted, and what it filed under each application, under that application.
         *
         * <p>The one way a reading made apart from this one is taken into it, so that what makes two
         * readings of a site, or of an application, one statement is decided by {@link #met} alone.
         */
        public void metAll(MeaningsOfABody reading) {
            reading.stated().forEach(this::met);
            reading.ambiguous().forEach(this::ambiguousAt);
            piecesAttempted.addAll(reading.piecesAttempted());
            reading.applications().forEach((which, on) -> onTheApplication(which).metAll(on));
        }

        /** {@code site} as one whose copies state different things, which states none of them. */
        private void ambiguousAt(Site site) {
            stated.remove(site);
            ambiguous.add(site);
        }

        /** What is filed under the application {@code which}. */
        private Filing onTheApplication(AnApplicationOfACall which) {
            return applications.computeIfAbsent(which, _ -> new Filing());
        }

        /**
         * What a closure's body states on each of its applications ({@code each}, one reading of the
         * body per application), met as what each site in it states on the application a run meets
         * it on ({@link Derivation.OnEachApplication}).
         *
         * <p>Not as copies of the site. A copy is the same construct met at another place, and two
         * copies stating different things are a site that says nothing; applications are one place
         * met with one value and then another, and stating different things on each is what such a
         * site does. A site with copies on some application is still a site with copies.
         *
         * <p>Each reading told apart from the others is filed as well, under which application it
         * is ({@link #metAll}), so a site met again on one application is what a site met again
         * anywhere is. The call that makes them is in the copy of the body it stands in, so the
         * applications a copy of a helper makes are not the ones another copy makes; a call that
         * applies two closures applies each of them on its first element, and the two readings
         * filed there state the sites of two bodies.
         */
        public void metOnEachApplication(List<ReadOnAnApplication> each) {
            List<MeaningsOfABody> readings =
                    each.stream().map(ReadOnAnApplication::reading).toList();
            readings.forEach(one -> piecesAttempted.addAll(one.piecesAttempted()));
            Set<Site> sites = new LinkedHashSet<>();
            readings.forEach(one -> {
                sites.addAll(one.stated().keySet());
                sites.addAll(one.ambiguous());
            });
            for (Site site : sites) {
                if (readings.stream().anyMatch(one -> one.ambiguous().contains(site))) {
                    ambiguousAt(site);
                    continue;
                }
                List<Derivation> how = readings.stream().map(one -> one.stated().get(site))
                        .filter(Objects::nonNull).map(Meaning::how).toList();
                met(site, new Conclusion(Optional.of(site.construct()))
                        .meaningOf(new Derivation.OnEachApplication(how)));
            }
            each.forEach(one -> one.which()
                    .ifPresent(which -> onTheApplication(which).metAll(one.reading())));
        }

        /** What was filed. */
        public MeaningsOfABody filed() {
            Map<AnApplicationOfACall, MeaningsOfABody> onEach = new LinkedHashMap<>();
            applications.forEach((which, filing) -> onEach.put(which, filing.filed()));
            return new MeaningsOfABody(stated, ambiguous, piecesAttempted, onEach);
        }
    }

    /**
     * What one reading of a closure's body states, and which application it was made on where
     * that is told ({@link InputReads.Applications.Made#which}).
     */
    public record ReadOnAnApplication(Optional<AnApplicationOfACall> which,
                                      MeaningsOfABody reading) {

        public ReadOnAnApplication {
            Objects.requireNonNull(which, "an application is told apart or is not");
            Objects.requireNonNull(reading, "a reading of the body was made on it");
        }
    }

    /**
     * What the body of a closure states on the application {@code which}: that application's own
     * reading, or empty where the body was not read on it alone.
     *
     * <p>For a reader that stands on that application, where a site states what the application
     * states and not what some application may. A reader that stands on no application in
     * particular reads {@link #at} as it is.
     */
    public Optional<MeaningsOfABody> onTheApplication(AnApplicationOfACall which) {
        return Optional.ofNullable(applications.get(which));
    }

    /** What is stated at {@code site}, or empty where nothing was read there or its copies state
     *  different things. */
    public Optional<Proposition> at(Site site) {
        return meaningAt(site).map(Meaning::states);
    }

    /** What is stated at {@code site} and how, or empty as {@link #at} is. */
    public Optional<Meaning> meaningAt(Site site) {
        return Optional.ofNullable(stated.get(site));
    }

    /** Why nothing is stated at {@code site}, where {@link #at} answers nothing. */
    public WhyUnread whyNothingAt(Site site) {
        return ambiguous.contains(site) ? new WhyUnread.CopiesStateDifferentThings()
                : new WhyUnread.NotMetByTheReading();
    }
}
