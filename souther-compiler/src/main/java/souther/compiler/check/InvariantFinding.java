package souther.compiler.check;

import souther.compiler.check.InvariantChecker.Judgment;
import souther.compiler.check.InvariantChecker.Verdict;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticPlace;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.msg.InvariantMessage;
import souther.compiler.diag.msg.Message;
import souther.compiler.diag.msg.Supporting;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashSet;
import java.util.Objects;
import java.util.Optional;
import java.util.SequencedMap;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Something the invariant check found at one construction, before anybody is sent anywhere.
 *
 * <p>What is to be reported and not the report. A finding says which type was being built, where in
 * this body it was built, and what was proved about each of the clauses it is held to
 * ({@link Judgment}) — every one of which is an answer about this module and about the declarations
 * as they read, and none of which is an answer about where anything is written. Where a clause is
 * written is asked of {@link ClauseLocations} by whoever is about to point at it, which is what that
 * says of itself.
 *
 * <p>Which is the whole reason this stands between the check and the diagnostic. Built straight into
 * a report, the check that decides whether a body is accepted also decides where a caret goes, and
 * so reads where every clause it judged is written: an edit that moves a clause and changes nothing
 * it states then reaches every body judged against it. The check keeping its answer and the caret
 * following the clause cannot both hold while one question answers both, and they are two questions.
 *
 * <p>Nothing here is handed out. A reader given the judgment would write the sentence again, and two
 * sentences about one finding are two answers to what this compiler says about it; the one way to
 * read a finding is {@link #reportedAs}, which is where all of it is decided.
 */
public final class InvariantFinding {

    private final TypeSymbol.AtModule type;
    private final SourcePos at;
    private final Judgment judgment;

    InvariantFinding(TypeSymbol.AtModule type, SourcePos at, Judgment judgment) {
        if (type == null || at == null || judgment == null) {
            throw new IllegalArgumentException("a finding is about a type being built somewhere,"
                    + " under what was proved of the clauses it is held to");
        }
        // A discharged invariant and one this check cannot express are silent, so there is nothing
        // to be reported and nothing here to report it. Which verdicts those are is the verdict's
        // own answer: asked by listing them here, this would be a second reading of the enum, and
        // the one that fell behind would either make a finding nobody can say or refuse one
        // somebody has to.
        if (judgment.verdict().holds()) {
            throw notSomethingToReport(judgment.verdict());
        }
        this.type = type;
        this.at = at;
        this.judgment = judgment;
    }

    /**
     * This finding as a report, pointing at the clauses it is about where {@code written} says they
     * are now.
     *
     * <p>Every sentence this check says is decided here, so which of them a finding comes out as is
     * read off the verdict once. A caller choosing the sentence and asking this to place the carets
     * would be the second reader of a judgment, and the two would agree only for as long as somebody
     * kept them so.
     */
    public Diagnostic reportedAs(ClauseLocations written) {
        return switch (judgment.verdict()) {
            // The clauses nothing known there establishes, which is what this warning is about.
            case UNKNOWN -> quoting(mayViolate()
                            .hint(new InvariantMessage.GuardItOrLetADataOwnTheRelation()),
                    judgment.unsettled(), new InvariantMessage.ThisClauseIsNotEstablishedHere(),
                    written);
            case REFUTED_ALONE -> refused(false, written);
            case REFUTED_NOT_ALONE -> refused(true, written);
            case PROVED, UNREPRESENTABLE -> throw notSomethingToReport(judgment.verdict());
        };
    }

    /**
     * The value fails the invariant, said in the terms the refutation was reached in: the value
     * alone fails it, or it fails under what else is known where it stands.
     *
     * <p>The message says what holds of every path, so it names the clauses the value fails wherever
     * it is built. Where there are none it names none, and the regions then carry a weaker claim
     * about a wider set: the clauses some path here fails. Two sets, because they are two claims —
     * pointing at those clauses under the sentence's own words would say of each that the value
     * fails it, which the value coming down the other branch refutes.
     */
    private Diagnostic refused(boolean onAPath, ClauseLocations written) {
        Diagnostic.Builder said = rejects(onAPath);
        return judgment.refuted().isEmpty()
                ? quoting(said, judgment.refutedSomewhere(),
                        new InvariantMessage.ThisClauseRejectsTheValueOnSomeOfThePathsHere(), written)
                : quoting(said, judgment.refuted(),
                        new InvariantMessage.ThisClauseRejectsThisValue(), written);
    }

    /**
     * Where the report is, and where the clauses it is about are written.
     *
     * <p>Both places, in one place, because a report that gave itself a position and stopped there
     * still reads as a report — nothing about a warning that points only at the construction says a
     * clause was left unpointed at. Every one of these comes through here, so a diagnostic this
     * check produces gets both or neither.
     *
     * <p>Which clauses is the caller's, and is not something this works out from a judgment: E2011
     * is about the clauses nothing known there establishes and E2010 about the ones the value fails,
     * and those are the two questions the classification was split to keep apart. What this does
     * with the clauses it is handed is the same either way — every one of them that this compile can
     * quote, in the order the clauses were declared, labelled with what the caller says of them.
     *
     * <p>A clause this compile has no file for is said rather than left out: the label says where
     * the code came from and points at nothing ({@link DiagnosticPlace}). It used to be dropped, so
     * the same warning about the same rule told a reader which clause was at issue when the
     * declaration was in this project and told them nothing when it came off the module path. What
     * the message says is a different question with a different answer — whether the clause could be
     * named — and neither decides the other.
     */
    private <M extends Message & Supporting> Diagnostic quoting(
            Diagnostic.Builder said, SequencedMap<Clause.Id, Clause.Ref> clauses, M label,
            ClauseLocations written) {
        said.at(at);
        // One label per place, and the clauses are what there are several of. A label is a sentence
        // about a place, and where two clauses are written in one module this compile has no file
        // for, the place is all either of them has: what told the two labels apart was the caret,
        // and there is no caret. Said once each they come out as the same sentence twice, which
        // reads as a repeat rather than as two clauses. Which clauses they are is in the message,
        // which names them.
        Set<DiagnosticPlace> already = new LinkedHashSet<>();
        Judgment.pointsTo(clauses, written).forEach(place -> {
            if (!already.add(place)) {
                return;
            }
            switch (place) {
                case DiagnosticPlace.InSource in -> said.secondary(in.region(), label);
                case DiagnosticPlace.Unavailable out -> said.secondaryOutOfSight(out.provenance(), label);
            }
        });
        return said.build();
    }

    /**
     * What a possible violation is said as, which is two questions and not one: whether a clause
     * nothing known there establishes can be named, and whether one that was established can be.
     * Neither answers the other, and neither answers whether there was such a clause — a clause
     * written without a name is judged like any other and is in no set here.
     *
     * <p>Asked one at a time and of the sets, before anything is written out. One joined string
     * answering both is what ended this warning with `Established here: .`, and it could as easily
     * have dropped an established clause a reader could have been told about: the two mistakes are
     * the same mistake, and they are the two spellings this did not have.
     */
    private Diagnostic.Builder mayViolate() {
        if (judgment.canNameUnsettled()) {
            if (judgment.canNameSettled()) {
                return Diagnostic.say(new InvariantMessage.NothingKnownHereEstablishesButDoesEstablish(
                        type.key().name(), names(judgment.unsettled()), names(judgment.settled())));
            }
            return Diagnostic.say(new InvariantMessage.NothingKnownHereEstablishes(
                    type.key().name(), names(judgment.unsettled())));
        }
        if (judgment.canNameSettled()) {
            return Diagnostic.say(
                    new InvariantMessage.NothingKnownHereEstablishesTheInvariantButDoesEstablish(
                            type.key().name(), names(judgment.settled())));
        }
        return Diagnostic.say(new InvariantMessage.NothingKnownHereEstablishesTheInvariant(
                type.key().name()));
    }

    /**
     * What a refuted invariant is said as. One question here and not two, because what this error
     * reports is the clause the value fails and nothing else.
     *
     * <p>Which is why it is the refuted clauses that are named and not the unsettled ones. A value
     * that fails one clause may leave others standing that nothing here decides, and those are
     * clauses nothing known there establishes rather than clauses the value fails — a sentence saying
     * "the value being built is one that clause rejects" over a list holding both says something
     * untrue of some of them.
     *
     * <p>A refuted invariant may well have clauses the guards established, and the judgment holds
     * their names when it does — E2010 does not report them, which is a decision about what this
     * diagnostic is for and not an observation that there were none. Anything that starts reporting
     * them here asks {@link Judgment#canNameSettled()}, as the warning does, rather than reading the
     * answer off the set it is already writing out.
     */
    private Diagnostic.Builder rejects(boolean onAPath) {
        if (onAPath) {
            return judgment.canNameRefuted()
                    ? Diagnostic.say(new InvariantMessage.TheValueIsRejectedOnAReachablePath(
                            type.key().name(), names(judgment.refuted())))
                    : Diagnostic.say(new InvariantMessage.TheValueIsRejectedOnAReachablePathUnnamed(
                            type.key().name()));
        }
        return judgment.canNameRefuted()
                ? Diagnostic.say(new InvariantMessage.TheValueIsOneTheInvariantRejects(
                        type.key().name(), names(judgment.refuted())))
                : Diagnostic.say(new InvariantMessage.TheValueIsOneTheInvariantRejectsUnnamed(
                        type.key().name()));
    }

    /**
     * The clause names as a diagnostic writes them out.
     *
     * <p>Reached only from a branch that has already chosen what to say. What decides which of the
     * spellings a diagnostic is written in is the set, and never this text: an empty string is what
     * a set with no names in it renders as, and reading it back as an answer puts "no clause was
     * named" and "there is no clause" into one value.
     */
    private static String names(SequencedMap<Clause.Id, Clause.Ref> clauses) {
        return clauses.values().stream().map(Clause.Ref::name).flatMap(Optional::stream)
                .map(ClauseName::value).collect(Collectors.joining(", "));
    }

    private static IllegalStateException notSomethingToReport(Verdict verdict) {
        return new IllegalStateException("a construction the check came to " + verdict
                + " about is one nothing is said about, so there is no finding to report");
    }

    /**
     * The same finding as another: the same construction, judged the same way.
     *
     * <p>A value, and one an answer about a body is kept or discarded by. Two runs of this check
     * over a body nothing about has changed find the same things, and a finding that compared by
     * identity would say otherwise — which would put an edit that moves a clause back on the reader
     * this stands between it and.
     */
    @Override
    public boolean equals(Object other) {
        return other instanceof InvariantFinding that
                && type.equals(that.type) && at.equals(that.at) && judgment.equals(that.judgment);
    }

    @Override
    public int hashCode() {
        return Objects.hash(type, at, judgment);
    }

    @Override
    public String toString() {
        return "InvariantFinding[" + type.key().name() + " at " + at + ", " + judgment + "]";
    }
}
