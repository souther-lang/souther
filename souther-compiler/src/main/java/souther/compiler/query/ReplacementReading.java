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

        /** The rewrite cannot be put to the rows, and why. */
        record CannotBeAsked(Why why) implements Standing {}

        /** Why a rewrite cannot be put to the rows. */
        enum Why {
            /** Carrying the sibling would grow the fork past what the classes allow. */
            TOO_LARGE,
            /** A row that states an answer could not be read, or neither held nor failed of the
             *  body as written, so whether it comes out differently under the rewrite is not
             *  known. */
            A_STATEMENT_WAS_NOT_READ,
            /** A row through the arm has no run under the rewrite that came back telling, so
             *  whether it comes out differently is not known. */
            A_RUN_DID_NOT_COME_BACK
        }
    }

    /** One rewrite and what the rows came to about it. */
    public record Account(Replacement replacement, Standing standing) {

        public Account {
            Objects.requireNonNull(replacement, "an account is of some rewrite");
            Objects.requireNonNull(standing, "an account says what the rows came to");
        }
    }

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
     * {@code wentThrough}, in the order the plan numbered the arms, or, where there are none, the
     * body answering each value a row came to.
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
        // The arms a row stating its answer went through. An arm no row reaches is owed a row under
        // its own code, and one only a row waiting for its answer reaches is too; a rewrite of
        // either is one no row could notice, and saying so would be the same gap said twice.
        Set<ArmProbe> reached = new HashSet<>();
        for (RowOutcome row : rows) {
            if (row.expectation() != ExpectationState.OWED) {
                reached.addAll(wentThrough.apply(row));
            }
        }
        List<Account> out = new ArrayList<>();
        Map<Replacement.OfAnArm, List<ArmProbe>> occurrences = new LinkedHashMap<>();
        for (CoverageSites.ArmSite site : plan.arms(behavior)) {
            if (site.place().probe().isEmpty() || !reached.contains(site.place().probe().get())) {
                continue;
            }
            ArmProbe probe = site.place().probe().get();
            List<ArmReplacements.AtSite> sites =
                    carried.ofArm(site.obligation().origin(), site.obligation().part());
            Set<Integer> withs = new TreeSet<>();
            sites.forEach(at -> withs.addAll(at.siblings().keySet()));
            for (int with : withs) {
                Replacement.OfAnArm replaced = new Replacement.OfAnArm(
                        site.obligation().origin(), site.obligation().part(), with);
                // The rewrite stands at every site of the arm at once, so it is the body under
                // another spelling only where it is at each of them.
                if (sites.stream().allMatch(at -> !at.siblings().containsKey(with)
                        || at.siblings().get(with).differs().provenAway(unreached))) {
                    continue;
                }
                occurrences.computeIfAbsent(replaced, _ -> new ArrayList<>()).add(probe);
            }
        }
        occurrences.forEach((replaced, where) -> out.add(new Account(replaced,
                armStanding(replaced, where, carried, rows, wentThrough))));
        // One answer only where no arm is rewritten. A body the rows go through a fork of is asked
        // about the fork, arm by arm. And not where the body answers one value already: every way
        // to an answer that reads something, or that is another answer, closed by the rules.
        if (occurrences.isEmpty() && !plan.fromOneValue(behavior).provenAway(unreached)) {
            out.addAll(oneAnswerAccounts(rows, comparing));
        }
        return List.copyOf(out);
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
        for (ArmReplacements.AtSite at : replacements.ofArm(replaced.fork(), replaced.part())) {
            if (at.siblings().get(replaced.with())
                    instanceof ArmReplacements.Sibling.NotCarried(var why, var _)) {
                return new Standing.CannotBeAsked(switch (why) {
                    case TOO_LARGE -> Standing.Why.TOO_LARGE;
                });
            }
        }
        RowIdentity shownBy = null;
        boolean unknown = false;
        for (RowOutcome row : rows) {
            if (row.expectation() == ExpectationState.OWED
                    || where.stream().noneMatch(wentThrough.apply(row)::contains)) {
                continue;
            }
            // A row that neither held nor failed of the body as written ran out or was given up
            // on, and is not run again: there is no way it came out to compare another with.
            if (row.disposition() != Disposition.HELD && row.disposition() != Disposition.FAILED) {
                unknown = true;
                continue;
            }
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
        if (unknown) {
            return new Standing.CannotBeAsked(Standing.Why.A_RUN_DID_NOT_COME_BACK);
        }
        ReplacementOwed lookFor = new ReplacementOwed.OfAnArm(replaced.fork(), replaced.part(),
                replaced.with(), where,
                replacements.replacing(replaced.fork(), replaced.part(), replaced.with()));
        return shownBy != null ? new Standing.Unnoticed(shownBy, lookFor)
                : new Standing.Open(lookFor);
    }

    /**
     * The body answering one value, once for each value a row answered: each is a program the body
     * could be rewritten as, and two of them are two programs. Told apart by a row that comes out
     * the other way against the value than it did against its own answer.
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
                out.add(new Account(rewrite,
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
            // A row whose answer is owed states nothing to fail.
            if (row.expectation() == ExpectationState.OWED) {
                continue;
            }
            // One whose statement was not carried states something, and nothing here can read
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
            return new Standing.CannotBeAsked(Standing.Why.A_STATEMENT_WAS_NOT_READ);
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
