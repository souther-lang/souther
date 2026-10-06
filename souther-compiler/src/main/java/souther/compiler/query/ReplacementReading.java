package souther.compiler.query;

import souther.compiler.core.Core;
import souther.compiler.coverage.ArmProbe;
import souther.compiler.coverage.ArmReplacements;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.observe.AnswerChange;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.Expectation;
import souther.compiler.observe.ExpectationState;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.ReplacedRun;
import souther.compiler.observe.RowIdentity;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.RowStatement;
import souther.compiler.partition.Replacement;
import souther.compiler.partition.ReplacementOwed;
import souther.compiler.types.BindingOwner;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.TreeMap;

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
            /** No row answered with a value read in full, so there is no answer to hold one to. */
            NOTHING_ANSWERED,
            /** A row that states an answer could not be read, or neither held nor failed of the
             *  body as written, so whether it comes out differently under the rewrite is not
             *  known. */
            A_STATEMENT_WAS_NOT_READ
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
     * came to about each: the siblings of each arm in {@code reached}, in the order the plan numbered
     * the arms, or, where there are none and {@code readsItsInput}, the body answering one value.
     *
     * <p>Only the arms a row reaches. What a rewrite of an arm asks is whether a row going through
     * it depends on what it answers, which is a question about the rows that go through it. The arms
     * are the ones the branch measure counts, wherever the helper they are written in is declared.
     */
    public static List<Account> of(String behavior, CoverageSites.Plan plan,
                                   Set<ArmProbe> reached, boolean readsItsInput,
                                   List<RowOutcome> rows, Comparing comparing) {
        List<Account> out = new ArrayList<>();
        Map<Replacement.OfAnArm, List<ArmProbe>> occurrences = new LinkedHashMap<>();
        Map<Replacement.OfAnArm, ArmReplacements.Sibling> siblings = new LinkedHashMap<>();
        for (CoverageSites.ArmSite site : plan.arms(behavior)) {
            if (site.place().probe().isEmpty() || !reached.contains(site.place().probe().get())) {
                continue;
            }
            ArmProbe probe = site.place().probe().get();
            ArmReplacements.AtSite at = plan.replacements()
                    .ofArm(site.obligation().origin(), site.obligation().part()).orElse(null);
            if (at == null) {
                continue;
            }
            new TreeMap<>(at.siblings()).forEach((with, sibling) -> {
                Replacement.OfAnArm replaced = new Replacement.OfAnArm(at.fork(), at.part(), with);
                occurrences.computeIfAbsent(replaced, _ -> new ArrayList<>()).add(probe);
                siblings.putIfAbsent(replaced, sibling);
            });
        }
        occurrences.forEach((replaced, where) -> out.add(new Account(replaced,
                armStanding(replaced, where, siblings.get(replaced), plan.replacements(), rows))));
        // One answer only where no arm is rewritten. A body the rows go through a fork of is asked
        // about the fork, arm by arm; asked for one answer as well, a body whose other arms nothing
        // can reach would be asked whether it is the constant it is, and no input would ever say.
        // And only where the body reads what it is given: one that does not answers one value
        // already, and that value is no rewrite of it.
        if (occurrences.isEmpty() && readsItsInput) {
            out.add(new Account(new Replacement.ByOneAnswer(), oneAnswerStanding(rows, comparing)));
        }
        return List.copyOf(out);
    }

    /**
     * Whether {@code body} reads any of the values {@code behavior} of {@code module} is given:
     * its parameters, and the ones a helper's expansion took in their place.
     */
    public static boolean readsItsInput(String module, String behavior, Core body) {
        BindingOwner signature = new BindingOwner.OfValue(module, behavior);
        if (body instanceof Core.Read read
                && (signature.equals(read.binding().owner())
                        || (read.binding().owner() instanceof BindingOwner.Synthesized written
                                && written.pass() == BindingOwner.Pass.INLINER
                                && signature.equals(written.within())))) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(body, child -> found[0] = found[0]
                || readsItsInput(module, behavior, child));
        return found[0];
    }

    private static Standing armStanding(Replacement.OfAnArm replaced, List<ArmProbe> where,
                                        ArmReplacements.Sibling sibling,
                                        ArmReplacements replacements, List<RowOutcome> rows) {
        if (sibling instanceof ArmReplacements.Sibling.NotCarried(var why)) {
            return new Standing.CannotBeAsked(switch (why) {
                case TOO_LARGE -> Standing.Why.TOO_LARGE;
            });
        }
        RowIdentity shownBy = null;
        for (RowOutcome row : rows) {
            for (ReplacedRun run : row.replaced()) {
                if (!run.fork().equals(replaced.fork()) || run.part() != replaced.part()
                        || run.with() != replaced.with()) {
                    continue;
                }
                if (run.noticed() == ReplacedRun.Noticed.YES) {
                    return new Standing.Noticed(row.identity());
                }
                if (shownBy == null && run.changed() == AnswerChange.CHANGED) {
                    shownBy = row.identity();
                }
            }
        }
        ReplacementOwed lookFor = new ReplacementOwed.OfAnArm(replaced.fork(), replaced.part(),
                replaced.with(), where,
                replacements.replacing(replaced.fork(), replaced.part(), replaced.with()));
        return shownBy != null ? new Standing.Unnoticed(shownBy, lookFor)
                : new Standing.Open(lookFor);
    }

    /**
     * The body answering one value: each value a row answered is a value the body could be
     * rewritten to answer always, and the rewrite is told apart by a row that comes out the other
     * way against that value than it did against its own answer. The first value no row comes out
     * differently against is the rewrite the rows leave standing.
     */
    private static Standing oneAnswerStanding(List<RowOutcome> rows, Comparing comparing) {
        List<RowOutcome> answered = new ArrayList<>();
        List<ObservedValue> values = new ArrayList<>();
        for (RowOutcome row : rows) {
            if (row.answer() instanceof AnswerObservation.Answered(ObservedValue value)
                    && AnswerChange.readInFull(value)) {
                answered.add(row);
                values.add(value);
            }
        }
        if (answered.isEmpty()) {
            return new Standing.CannotBeAsked(Standing.Why.NOTHING_ANSWERED);
        }
        List<ObservedValue> distinct = new ArrayList<>();
        for (ObservedValue value : values) {
            if (distinct.stream().noneMatch(each -> comparing.same(each, value))) {
                distinct.add(value);
            }
        }
        RowIdentity noticedBy = null;
        for (ObservedValue always : distinct) {
            RowIdentity failing = null;
            boolean unread = false;
            for (RowOutcome row : rows) {
                // A row whose answer is owed states nothing to fail.
                if (row.expectation() == ExpectationState.OWED) {
                    continue;
                }
                // One whose statement was not carried states something, and nothing here can
                // read what. Nor can one that neither held nor failed of the body as written.
                if (!(row.statement() instanceof RowStatement.Stated stated)
                        || !(stated.expects() instanceof Expectation.Asserts asserts)
                        || (row.disposition() != Disposition.HELD
                                && row.disposition() != Disposition.FAILED)) {
                    unread = true;
                    continue;
                }
                // Told apart by ending the other way under the rewrite, as a run of it is.
                if (comparing.holds(asserts, always)
                        != (row.disposition() == Disposition.HELD)) {
                    failing = row.identity();
                    break;
                }
            }
            if (failing != null) {
                if (noticedBy == null) {
                    noticedBy = failing;
                }
                continue;
            }
            if (unread) {
                return new Standing.CannotBeAsked(Standing.Why.A_STATEMENT_WAS_NOT_READ);
            }
            for (int i = 0; i < answered.size(); i++) {
                if (!comparing.same(values.get(i), always)) {
                    return new Standing.Unnoticed(answered.get(i).identity(),
                            new ReplacementOwed.ByOneAnswer(always));
                }
            }
            return new Standing.Open(new ReplacementOwed.ByOneAnswer(always));
        }
        return new Standing.Noticed(noticedBy);
    }

    private ReplacementReading() {}
}
