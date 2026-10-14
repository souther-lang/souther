package souther.compiler.query;

import souther.compiler.coverage.ArmProbe;
import souther.compiler.coverage.ArmReplacements;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.observe.AnswerChange;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.Expectation;
import souther.compiler.observe.ExpectationState;
import souther.compiler.observe.Figure;
import souther.compiler.observe.Limits;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.ReplacedRun;
import souther.compiler.observe.RowIdentity;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.RowStatement;
import souther.compiler.partition.Replacement;
import souther.compiler.observe.RowRef;
import souther.compiler.partition.ReplacementOwed;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * What a behavior's written rows came to about each rewrite of its body a row could notice.
 *
 * <p>Two families of rewrite and no more. An arm answering as one of its siblings does is the
 * rewrite a fork invites; the body answering one value whatever it is given is the rewrite a body
 * with no fork in it invites, and the one rows that all answer alike cannot tell from it. Which
 * rewrites are asked about is fixed here and not read off how the body happens to be lowered, so a
 * change of the library under a body is not a change of what its rows are held to.
 *
 * <p>A row is evidence against a rewrite where it comes out the other way under it: what it states
 * holds of one of the two bodies and fails of the other. A row wrong about both is evidence for
 * neither. A rewrite no row notices is a gap only where some run shows it answers differently from the body, since one
 * that answers alike everywhere is the body under another spelling and no row could notice it; and
 * where nothing shows that, what is left is a search for an input that would.
 */
public final class ReplacementReading {

    /** What the written rows came to about one rewrite. */
    public sealed interface Standing {

        /** A row comes out the other way under the rewrite: the row tells it from the body. */
        record Noticed(RowIdentity by) implements Standing {}

        /** A row's run of the rewrite answered differently from the body, and no row came out
         *  differently under it; {@code lookFor} is the rewrite as a search for a row telling it
         *  apart is put to it. */
        record Unnoticed(RowIdentity shownBy, ReplacementOwed lookFor) implements Standing {}

        /** No row came out differently under the rewrite and no run showed it answering
         *  differently: what is left to ask is whether any input would. */
        record Open(ReplacementOwed lookFor) implements Standing {}

        /**
         * The rewrite cannot be put to the rows, and why, as the place that found it so: the
         * classes not carrying the sibling, a row whose statement could not be read, or a row
         * through the arm with no run under the rewrite that came back telling.
         */
        record CannotBeAsked(ReplacementEvidence.Undecided.LeftOpen why) implements Standing {

            public CannotBeAsked {
                Objects.requireNonNull(why, "a rewrite that cannot be asked about says why");
            }

            /** One way, as the place that found it so. */
            CannotBeAsked(ReplacementEvidence.Undecided.Way why) {
                this(ReplacementEvidence.Undecided.LeftOpen.of(List.of(why)));
            }
        }
    }

    /** One rewrite, where a report about it is shown, and what the rows came to about it. */
    public record Account(Replacement replacement, ReplacementReportAnchor reportAt,
                          Standing standing) {

        public Account {
            Objects.requireNonNull(replacement, "an account is of some rewrite");
            Objects.requireNonNull(reportAt, "and is shown somewhere");
            Objects.requireNonNull(standing, "an account says what the rows came to");
            if (!reportAt.shows(replacement)) {
                throw new IllegalArgumentException(replacement + " is not shown at " + reportAt);
            }
        }
    }

    /** The places in the plan one rewrite of an arm stands at, and the one place it is shown. */
    private record Occurrences(ReplacementReportAnchor reportAt, List<ArmProbe> probes) {}

    /**
     * What being the same answer means for the behavior: two values read in full, and a statement
     * against a value, both read with the declarations and at the behavior's answer.
     */
    public interface Comparing {

        boolean same(ObservedValue left, ObservedValue right);

        /** Whether {@code stated} holds of {@code answered}. */
        boolean holds(Expectation.Asserts stated, ObservedValue answered);
    }

    /**
     * Every rewrite of {@code behavior}'s body {@code plan} can put to a row, and what {@code rows}
     * came to about each: the siblings of each arm a row stating its answer went through, by
     * {@code wentThrough}, in the order the plan numbered the arms, or, where no arm of the body has
     * a rewrite that is another program, the body answering each value a row stating its answer
     * came to.
     *
     * <p>Only the arms a row reaches. What a rewrite of an arm asks is whether a row going through
     * it depends on what it answers, which is a question about the rows that go through it. The arms
     * are the ones the branch measure counts, wherever the helper they are written in is declared.
     *
     * <p>And only the rewrites that are other programs. A rewrite every way of which that could
     * part it from the body goes through an arm {@code unreached} answers for is the body under
     * another spelling — a proof, read off the source and the model's own rules — and no row is
     * owed for it. Nothing else here concludes that: a search finding no input the two part at
     * leaves the rewrite open.
     *
     * <p>Which siblings there are is {@code carried}, what the classes the rows ran in hold, and
     * not the plan's: a fork a method could not hold its siblings in was written without them, and
     * a rewrite there is one no run could be asked for.
     */
    public static List<Account> of(String behavior, CoverageSites.Plan plan,
                                   ArmReplacements carried,
                                   Function<RowOutcome, Set<ArmProbe>> wentThrough,
                                   Predicate<ControlPlace.Arm> unreached,
                                   List<RowOutcome> rows, Comparing comparing) {
        // The rows that state their answer, which are the only evidence about a rewrite there is.
        // A row whose answer is owed ran, and what it ran to is an observation and not what the
        // model owes there — so it is evidence for neither the body nor the rewrite, on either side
        // of the comparison. What it is owed is its answer, which the account of rows asks for.
        List<RowOutcome> stated = rows.stream()
                .filter(row -> row.expectation() == ExpectationState.NOT_OWED).toList();
        // The arms a row stating its answer went through. An arm no row reaches is owed a row under
        // its own code, and one only a row waiting for its answer reaches is too; a rewrite of
        // either is one no row could notice, and saying so would be the same gap said twice.
        Set<ArmProbe> reached = new HashSet<>();
        for (RowOutcome row : stated) {
            reached.addAll(wentThrough.apply(row));
        }
        List<Account> out = new ArrayList<>();
        Map<Replacement.OfAnArm, Occurrences> occurrences = new LinkedHashMap<>();
        // Whether some arm of the body has a rewrite that is another program, which is what makes
        // the body one with a fork as far as a rewrite goes: a fork every rewrite of which the
        // source and the rules prove is the body under another spelling invites none, and the body
        // is then asked about as one with no fork. Settled by the body and the rules, and never by
        // which arms the rows stating an answer reached.
        boolean forked = false;
        for (CoverageSites.ArmSite site : plan.arms(behavior)) {
            if (site.place().probe().isEmpty()) {
                continue;
            }
            List<ArmReplacements.AtSite> sites =
                    carried.ofArm(site.obligation().origin(), site.obligation().part());
            List<Integer> withs = otherPrograms(sites, unreached);
            forked = forked || !withs.isEmpty();
            ArmProbe probe = site.place().probe().get();
            if (!reached.contains(probe)) {
                continue;
            }
            ReplacementReportAnchor reportAt = ReplacementReportAnchor.ofAnArm(site.anchor());
            for (int with : withs) {
                Replacement.OfAnArm replaced = new Replacement.OfAnArm(
                        site.obligation().origin(), site.obligation().part(), with);
                Occurrences at = occurrences.computeIfAbsent(replaced,
                        _ -> new Occurrences(reportAt, new ArrayList<>()));
                // One fork is in a source this compilation holds or it is not, whichever call
                // reached it; two answers would be the plan disagreeing with itself about the fork.
                if (!at.reportAt().equals(reportAt)) {
                    throw new IllegalStateException(replaced + " is shown at " + at.reportAt()
                            + " where one call reaches it and at " + reportAt + " where another"
                            + " does");
                }
                at.probes().add(probe);
            }
        }
        occurrences.forEach((replaced, at) -> out.add(new Account(replaced, at.reportAt(),
                armStanding(replaced, at.probes(), carried, stated, wentThrough))));
        // One answer only where no arm has a rewrite that is another program. Which family a body
        // invites is the body's: one with a fork is asked about the fork, arm by arm, whichever of
        // its arms the rows stating an answer happen to reach — read off what they reached
        // instead, a body every row of which is waiting for its answer would be asked as though it
        // had no fork, and its answers so far would be called rewrites. And not where the body
        // answers one value already: every way to an answer that reads something, or that is
        // another answer, closed by the rules.
        if (!forked && !plan.fromOneValue(behavior).provenAway(unreached)) {
            out.addAll(oneAnswerAccounts(stated, comparing));
        }
        return List.copyOf(out);
    }

    /**
     * The siblings an arm at {@code sites} can be rewritten as that are other programs, in the
     * order of their parts.
     *
     * <p>A rewrite stands at every site of the arm at once, so it is the body under another
     * spelling only where it is at each of them: where every site either lacks the sibling or has
     * it proven to part from the arm only on ways {@code unreached} answers for.
     */
    private static List<Integer> otherPrograms(List<ArmReplacements.AtSite> sites,
                                               Predicate<ControlPlace.Arm> unreached) {
        Set<Integer> withs = new TreeSet<>();
        sites.forEach(at -> withs.addAll(at.siblings().keySet()));
        List<Integer> out = new ArrayList<>();
        for (int with : withs) {
            if (!sites.stream().allMatch(at -> !at.siblings().containsKey(with)
                    || at.siblings().get(with).differs().provenAway(unreached))) {
                out.add(with);
            }
        }
        return out;
    }

    /**
     * What the rows came to about one rewrite of an arm.
     *
     * <p>Every row that went through the arm and states something is asked, and one that ran out —
     * as written or under the rewrite — may be the row that tells it apart, so the rewrite is left
     * undecided rather than called unnoticed on the strength of the rows that did come back.
     */
    private static Standing armStanding(Replacement.OfAnArm replaced, List<ArmProbe> where,
                                        ArmReplacements replacements, List<RowOutcome> rows,
                                        Function<RowOutcome, Set<ArmProbe>> wentThrough) {
        // Every site, since a rewrite stands at all of them at once: a site the JVM could not hold
        // the sibling at leaves it unasked whatever a wider run lets the other forks carry.
        List<ArmReplacements.Sibling.Why> notCarried = new ArrayList<>();
        for (ArmReplacements.AtSite at : replacements.ofArm(replaced.fork(), replaced.part())) {
            if (at.siblings().get(replaced.with())
                    instanceof ArmReplacements.Sibling.NotCarried(
                            ArmReplacements.Sibling.Why why, ArmReplacements.Differs _)) {
                notCarried.add(why);
            }
        }
        if (!notCarried.isEmpty()) {
            List<ReplacementEvidence.Undecided.Way> ways = new ArrayList<>();
            for (ArmReplacements.Sibling.Why why : notCarried) {
                ways.add(wayOf(why));
            }
            return new Standing.CannotBeAsked(ReplacementEvidence.Undecided.LeftOpen.of(ways));
        }
        RowIdentity shownBy = null;
        boolean unknown = false;
        List<List<ObservedValue>> seenThrough = new ArrayList<>();
        for (RowOutcome row : rows) {
            if (where.stream().noneMatch(wentThrough.apply(row)::contains)) {
                continue;
            }
            // A row that neither held nor failed of the body as written ran out or was given up
            // on, and is not run again: there is no way it came out to compare another with.
            if (row.disposition() != Disposition.HELD && row.disposition() != Disposition.FAILED) {
                unknown = true;
                continue;
            }
            seenThrough.add(row.inputs());
            // Every rewrite of every arm a decided row went through was run, or is said to have
            // run out, so one missing is this reading and the run disagreeing about what was
            // carried — not something to read a reason off.
            ReplacedRun run = row.replaced().stream()
                    .filter(each -> each.fork().equals(replaced.fork())
                            && each.part() == replaced.part() && each.with() == replaced.with())
                    .findFirst().orElseThrow(() -> new IllegalStateException("row `"
                            + row.identity().shown() + "` went through " + replaced
                            + " and carries no run of it: " + row.replaced()));
            if (run.noticed() == ReplacedRun.Noticed.COULD_NOT_TELL) {
                unknown = true;
                continue;
            }
            if (run.noticed() == ReplacedRun.Noticed.YES) {
                return new Standing.Noticed(row.identity());
            }
            if (shownBy == null && run.changed() == AnswerChange.CHANGED) {
                shownBy = row.identity();
            }
        }
        // What stopped those runs is not carried past what they answered, so this names no figure
        // ({@link ReplacementEvidence.Undecided.Way.AtAnAllowanceNotCarried}).
        if (unknown) {
            return new Standing.CannotBeAsked(
                    new ReplacementEvidence.Undecided.Way.AtAnAllowanceNotCarried(
                            ReplacementEvidence.Undecided.Why.A_RUN_DID_NOT_COME_BACK));
        }
        ReplacementOwed lookFor = new ReplacementOwed.OfAnArm(replaced.fork(), replaced.part(),
                replaced.with(), where,
                replacements.replacing(replaced.fork(), replaced.part(), replaced.with()),
                seenThrough);
        return shownBy != null ? new Standing.Unnoticed(shownBy, lookFor)
                : new Standing.Open(lookFor);
    }

    /**
     * What a sibling the classes do not carry leaves a rewrite as: open at the figure a fork was
     * held to, which a wider run raises, or at what the JVM holds in one method, which no run of
     * this compiler widens. Both are published as one reason.
     */
    static ReplacementEvidence.Undecided.Way wayOf(ArmReplacements.Sibling.Why why) {
        return switch (why) {
            case ArmReplacements.Sibling.Why.PastWhatAForkCarries(Figure limit) ->
                    new ReplacementEvidence.Undecided.Way.AtFigures(
                            ReplacementEvidence.Undecided.Why.TOO_LARGE, List.of(limit));
            case ArmReplacements.Sibling.Why.PastWhatAMethodHolds _ ->
                    new ReplacementEvidence.Undecided.Way.AtNoAllowance(
                            ReplacementEvidence.Undecided.Why.TOO_LARGE);
        };
    }

    /**
     * The body answering one value, once for each value a row stating its answer answered: each is
     * a program the body could be rewritten as, and two of them are two programs. Told apart by a
     * row that comes out the other way against the value than it did against its own answer.
     *
     * <p>{@code rows} are the rows stating an answer and no others. A row waiting for its answer
     * ran to a value, and a rewrite built from that value — or held unnoticed because that row
     * answered something else — would be asking for a row the account of rows already asks for, at
     * the input of a row already written.
     *
     * <p>A value a row answered in full is one of these, and nothing else is: a value cut short
     * anywhere inside is not one a body could be rewritten to answer, since nothing here knows what
     * it is.
     */
    private static List<Account> oneAnswerAccounts(List<RowOutcome> rows,
                                                   Comparing comparing) {
        List<RowOutcome> answered = new ArrayList<>();
        List<ObservedValue> values = new ArrayList<>();
        for (RowOutcome row : rows) {
            if (row.answer() instanceof AnswerObservation.Answered(ObservedValue value)
                    && Limits.UNBOUNDED.admits(value)) {
                answered.add(row);
                values.add(value);
            }
        }
        List<Account> out = new ArrayList<>();
        List<ObservedValue> distinct = new ArrayList<>();
        for (int i = 0; i < values.size(); i++) {
            ObservedValue value = values.get(i);
            if (distinct.stream().noneMatch(each -> comparing.same(each, value))) {
                distinct.add(value);
                Replacement.ByOneAnswer rewrite = new Replacement.ByOneAnswer(value,
                        RowRef.of(answered.get(i)));
                out.add(new Account(rewrite, new ReplacementReportAnchor.AtTheBehavior(),
                        oneAnswerStanding(rewrite, rows, answered, values, comparing)));
            }
        }
        return List.copyOf(out);
    }

    /** What the rows came to about the body answering {@code rewrite}'s value always. */
    private static Standing oneAnswerStanding(Replacement.ByOneAnswer rewrite,
                                              List<RowOutcome> rows, List<RowOutcome> answered,
                                              List<ObservedValue> values, Comparing comparing) {
        ObservedValue always = rewrite.answer();
        boolean unread = false;
        for (RowOutcome row : rows) {
            // A row whose statement was not carried states something, and nothing here can read
            // what. Nor can one that neither held nor failed of the body as written.
            if (!(row.statement() instanceof RowStatement.Stated stated)
                    || !(stated.expects() instanceof Expectation.Asserts asserts)
                    || (row.disposition() != Disposition.HELD
                            && row.disposition() != Disposition.FAILED)) {
                unread = true;
                continue;
            }
            // Told apart by ending the other way under the rewrite, as a run of it is.
            if (comparing.holds(asserts, always) != (row.disposition() == Disposition.HELD)) {
                return new Standing.Noticed(row.identity());
            }
        }
        if (unread) {
            return new Standing.CannotBeAsked(new ReplacementEvidence.Undecided.Way.AtNoAllowance(
                    ReplacementEvidence.Undecided.Why.A_STATEMENT_WAS_NOT_READ));
        }
        // A row whose own answer was another value is a run the rewrite answers differently.
        for (int i = 0; i < answered.size(); i++) {
            if (!comparing.same(values.get(i), always)) {
                return new Standing.Unnoticed(answered.get(i).identity(),
                        new ReplacementOwed.ByOneAnswer(rewrite));
            }
        }
        return new Standing.Open(new ReplacementOwed.ByOneAnswer(rewrite));
    }

    private ReplacementReading() {}
}
