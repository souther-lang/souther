package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.types.Type;
import souther.compiler.values.AdmissibleValues;
import souther.compiler.values.AdmittedPlan;
import souther.compiler.values.Allowance;
import souther.compiler.values.Emptiness;
import souther.compiler.values.Realizations;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * What the clauses of one rule say, in each of the languages a clause is read in.
 *
 * <p>Two languages and one reading. Which values a position may take is a set, and where a position
 * stops is a range, and neither says what the other says — an ordering names no finite set, and a
 * set of values has no word for what lies between two of them. So a clause reaches whichever of them
 * has a word for it, and some clauses reach both.
 *
 * <p><b>One rule's, and never met with another rule's.</b> This tree answers what one rule's own
 * clauses took in, and that answer must come from those clauses alone — a constraint a neighbouring
 * rule states does not change what this one read, however much it changes what the value admits. So
 * the conjunction across rules is not written over this type at all: the value derivation is a
 * projection ({@link #together()}) onto {@link StatedTogether}, which is where clauses meet, and
 * the one thing this tree takes back from there is the fate of its own choices
 * ({@link Settlement}). The conjunction inside one clause exists only inside the fold that reads
 * the clause ({@code Reading}), so there is no operation on this type by which a neighbouring
 * rule's reading could arrive.
 *
 * <p><b>The connectives are over this and not over either of them.</b> A choice between two
 * alternatives is a choice between two readings of the whole value, so an alternative that cannot be
 * taken is dropped by asking the whole of what is known about it
 * ({@link souther.compiler.values.PlannedValues#holdsNothingAsBuilt}). Applied
 * inside each language on its own, the drop happened only where the language doing the joining was
 * also the one that could show the branch impossible: {@code s < "" || (b == true && b == false)}
 * has a branch no order admits beside a branch no set of values admits, and each language, joining
 * alone, found nothing wrong with the branch the other one had refused. The same shape appears
 * inside one language across two positions, since a join keeps only what both sides spoke about.
 *
 * <p><b>Two of the four domains of {@link ConstraintState} are not here, and it is not an
 * oversight.</b> The interval algebra and the predicates are what a construction owes
 * ({@link Predicates}), which is a different question about the same clause: an alternative owes a
 * construction nothing a guard could discharge, so neither of them ever reads a branch of a choice.
 * A branch impossible only by an arithmetic relation between two positions is one nothing here can
 * drop, and giving those two a reading of alternatives is its own change with its own reason.
 */
sealed interface StatedByClauses {

    /**
     * What the clauses read so far leave, in both languages, with the account of what each took in.
     *
     * <p>Everything a choice could settle has been settled: what is here is one reading and not a
     * question about which of two it turned out to be.
     */
    record Said(souther.compiler.values.PlannedValues<FactSubject> values,
                OrderedIntervals<FactSubject> ordered,
                Adoption<FactSubject> byValues, Adoption<FactSubject> byOrder,
                Map<FactSubject, StringRestriction> strings,
                Map<Core, Part> parts)
            implements StatedByClauses, Confinement<FactSubject> {

        /**
         * What the values leave, as far as that is settled without building anything.
         *
         * <p>The same answer {@link StatedTogether.Said} gives of the same pair, this being the
         * account's copy of it. A description of what a position admits is not a set, so the
         * alternatives cannot be asked where their positions stop until one is built, and building
         * one here would spend the budget the answer is bounded by to write an account.
         */
        @Override
        public Emptiness ofTheValues() {
            return values.emptiness();
        }

        /** The same, out of what was built for the positions rather than by building. */
        @Override
        public Emptiness ofTheValuesAlreadyBuilt(Allowance<FactSubject> by) {
            return values.holdsNothingAsBuilt(by) ? Emptiness.EMPTY : Emptiness.UNDECIDED;
        }

        // No copy on the way in. The parts are filed by the node itself and not by what a node is
        // equal to — two conjuncts written the same way are two places in a clause — so the map is
        // one that compares by identity, and a copy of it would not be.

        /** The same, remembering that it is what {@code e} came to. */
        @Override
        public StatedByClauses from(Core e) {
            Map<Core, Part> out = new java.util.IdentityHashMap<>(parts);
            out.put(e, new Part(byValues, byOrder, values.standing(), strings));
            return new Said(values, ordered, byValues, byOrder, strings, out);
        }
    }

    /**
     * What one part of a clause came to, kept where the whole reading keeps everything else.
     *
     * <p>Carried rather than asked for. Which branch of a choice anybody can be in is settled by
     * the rules of every clause together, and a part read again on its own is read against a tree
     * that decision never reached — so it answers about a branch the declaration has already
     * dropped, and it pays to find out.
     *
     * <p>What is here is what a reader of the account needs of a part: which positions each
     * language took it in at, and what it wrote down about the ones it could not. What the part
     * finally admits is not among them — that is the whole value's answer and belongs to the whole.
     *
     * @param standing what this part's reading recorded about positions it was short of
     * @param aboutStrings what this part states about the strings at each position it states a rule
     *                     about. The position is here whether or not the rule was read, because
     *                     which of a position's numbers a rule is written about is settled by the
     *                     call; what the rule leaves is the other half, and a rule this could not
     *                     read has none
     */
    record Part(Adoption<FactSubject> byValues, Adoption<FactSubject> byOrder,
                Map<FactSubject, java.util.List<souther.compiler.values.UnreadReason>> standing,
                Map<FactSubject, StringRestriction> aboutStrings) {

        /** The same part, in a branch nobody can be in — see {@link Adoption#inADeadBranch}. */
        Part inADeadBranch() {
            // The reasons go with it too. A rule of a branch nothing satisfies is not a rule of
            // this declaration that went unread; there is no branch for an author to look at.
            //
            // And neither is what it said about the strings at a position. A line drawn from a
            // branch nobody can be in is a line the model does not draw.
            return new Part(byValues.inADeadBranch(), byOrder.inADeadBranch(), Map.of(), Map.of());
        }

        /** This part of the branch that stands, beside the same part of one nobody can be in. */
        Part beside(Part gone) {
            return new Part(byValues.beside(gone.byValues()), byOrder.beside(gone.byOrder()),
                    standing, aboutStrings);
        }

        /** The same part of two branches, neither of which anybody can be in. */
        Part bothDead(Part other) {
            return new Part(byValues.bothDead(other.byValues()),
                    byOrder.bothDead(other.byOrder()), Map.of(), Map.of());
        }

        /** The same part of two branches somebody can be in. */
        Part either(Part other) {
            Map<FactSubject, java.util.List<souther.compiler.values.UnreadReason>> why =
                    ReadByClauses.alsoSaying(standing, other.standing());
            // What an unread alternative does to the reasons is the vocabulary's rule, stated once
            // ({@code UnreadReason.leftOpen}); which positions it happens to is this carrier's.
            // What this side's copy reached — not what it settled: a position a dead branch
            // settled is an answer, and an unread alternative widens a constraint, not an answer
            // ({@link Adoption#either} makes the same distinction).
            if (other.byValues().dropped()) {
                why = souther.compiler.values.UnreadReason.leftOpen(why, reachedBy(byValues()));
            }
            if (byValues().dropped()) {
                why = souther.compiler.values.UnreadReason.leftOpen(why,
                        reachedBy(other.byValues()));
            }
            return new Part(byValues.either(other.byValues()), byOrder.either(other.byOrder()),
                    why, StringRestriction.over(aboutStrings, other.aboutStrings(), false));
        }

        /** The positions a rule of this copy reached and did not merely settle: what it
         *  constrained, and what it was about and could not manage. */
        private static java.util.Set<FactSubject> reachedBy(Adoption<FactSubject> of) {
            java.util.Set<FactSubject> out = new java.util.LinkedHashSet<>(of.read());
            out.addAll(of.missed());
            return out;
        }

    }

    /**
     * A choice whose branches this cannot tell apart yet.
     *
     * <p>An interpreted connective and not an unread one: the clause said {@code ||} and this is
     * what {@code ||} means, held open because whether anybody can be in a branch is settled by the
     * rules of every clause together — a clause written later can be the one that shows a branch
     * here impossible, and where the choice was decided over what this clause happened to hold,
     * that clause's refinement had nothing to reach. It carries the id of the written {@code ||},
     * which is how the fate settled over the whole declaration finds its way back to this tree.
     *
     * <p><b>The whole of what was read, and not its values alone.</b> A branch is dropped, kept, or
     * kept beside a dead one, and every part of a reading is answered differently by each of those
     * — what the positions admit, where they stop, and which rules each language took in. Held open
     * for the values while the rest was settled, a branch that turned out dead left its adoption
     * behind: the account said a rule of a branch nothing satisfies had gone unread, and there was
     * no branch for an author to go and look at.
     */
    record Choice(ChoiceId id, StatedByClauses left, StatedByClauses right)
            implements StatedByClauses {

        public Choice {
            if (id == null || left == null || right == null) {
                throw new IllegalArgumentException("a choice is between two named readings");
            }
        }

        /** Into both branches, since which of them survives is not known yet. */
        @Override
        public StatedByClauses from(Core e) {
            return new Choice(id, left.from(e), right.from(e));
        }
    }

    /** Nothing read, so nothing ruled out. */
    static StatedByClauses top() {
        return new Said(souther.compiler.values.PlannedValues.top(),
                OrderedIntervals.top(),
                Adoption.nothing(), Adoption.nothing(), Map.of(), Map.of());
    }

    /**
     * Whether anything satisfies what has been read, as far as that is settled.
     *
     * <p>A choice is either of its branches; a reading is what its two languages leave between them,
     * which is one answer and is {@link Confinement}'s. Asked of the languages one at a time, this
     * said that something satisfies the rules whenever the language it happened to ask had nothing
     * to say about them.
     */
    default Emptiness emptiness() {
        return switch (this) {
            case Choice it -> it.left().emptiness().joined(it.right().emptiness());
            case Said it -> it.admits();
        };
    }

    /**
     * The same reading, remembering that it is what {@code e} came to.
     *
     * <p>Into every branch of a choice this could not settle, because which of them survives is not
     * known yet and the part is in each of them until it is. Recorded on the outside instead, a part
     * whose branch turns out dead is a part nothing transformed, and the account it gives is the one
     * it gave before anybody knew.
     *
     */
    StatedByClauses from(Core e);

    /**
     * What this rule's own clauses leave, with its choices decided by its own clauses and by
     * nothing that was built for the account.
     *
     * <p>The rule alone, which is what a reader asking what <em>this</em> rule did to a position has
     * to be given. A branch its neighbours refuse is theirs to refuse, and a reading that took the
     * declaration's fates would hand this rule their narrowing.
     *
     * <p>Its own branches are dropped where something has already established that nobody can be in
     * them — off the descriptions where they say so, and otherwise off what the position's answer
     * was built to be. Nothing is built here: an account that paid for a machine would be spending
     * the budget the answer is bounded by, and a limit met while attributing a reason would come out
     * as this compiler being less able to answer about the model.
     *
     * <p>So a branch nothing has shown impossible is kept, and the rule reads as one that leaves
     * the position wider. That is an account declining to claim what nothing established, which is
     * the direction an account has to fail in.
     *
     * <p><b>Both languages, and the whole of what is known, which is what a fate is asked of.</b>
     * A branch is one nobody can be in where either language says so, and each of them is short of
     * what the other holds: {@code (n < 0 || String.matches("C", s)) && n > 1} has a branch no order
     * admits, and a fold that asked the values alone would find nothing wrong with it and lose what
     * the rule states about {@code s}. That is the same drop this type's connectives are over
     * rather than either language's, said of a rule read on its own.
     */
    default StatedTogether.Said alone(
            Alternatives held, souther.compiler.values.Allowance<FactSubject> by) {
        return switch (this) {
            case Said it -> new StatedTogether.Said(it.values(), it.ordered());
            case Choice it -> {
                StatedTogether.Said one = it.left().alone(held, by);
                StatedTogether.Said other = it.right().alone(held, by);
                boolean hereIsEmpty = nobodyIsIn(one, by);
                boolean thereIsEmpty = nobodyIsIn(other, by);
                if (thereIsEmpty) {
                    yield one;
                }
                if (hereIsEmpty) {
                    yield other;
                }
                yield new StatedTogether.Said(
                        held == Alternatives.APART
                                ? one.values().joinApart(other.values())
                                : one.values().join(other.values()),
                        one.ordered().join(other.ordered()));
            }
        };
    }

    /**
     * Whether something has already established that nobody can be in {@code branch}.
     *
     * <p>The two languages together ({@link Confinement}), and established rather than worked out:
     * an order is bottom or it is not, a description of values says so or waits, and where it waits
     * this asks what was already built for the position rather than building it.
     */
    private static boolean nobodyIsIn(StatedTogether.Said branch,
                                      souther.compiler.values.Allowance<FactSubject> by) {
        return branch.alreadyEstablished(by) == Emptiness.EMPTY;
    }

    /**
     * The same clauses with the account left behind, which is what the rules of a declaration are
     * met over.
     *
     * <p>A projection and not a second reading: the values and the ranges are the ones this holds,
     * and the choices keep their ids, so a fate settled over there names a choice here.
     */
    default StatedTogether together() {
        return switch (this) {
            case Said it -> new StatedTogether.Said(it.values(), it.ordered());
            case Choice it -> new StatedTogether.Choice(it.id(),
                    it.left().together(), it.right().together());
        };
    }

    /** The reading of one value's positions, made once and used over however many clauses reach it.
     *  Built per clause, this walk paid for a pair of readers at every clause of every value. */
    static Reading readingOf(Terms terms, Map<FactSubject, Type> byName,
                             Symbols symbols, Alternatives alternatives,
                             souther.compiler.values.Allowance<FactSubject> allowed) {
        return new Reading(AdmissibleReading.of(terms, byName, symbols, alternatives, allowed),
                OrderedReading.of(terms, byName, symbols), terms, byName, alternatives);
    }




    /**
     * The two readings of one clause tree, run together so that the connectives are the clause's,
     * and where they took a leaf in.
     *
     * <p>{@code adopted} is filled by the readings as they read, and is theirs to say. Read off
     * what a reading leaves a position instead, a clause it took in whole and narrowed nothing by
     * comes back unread: {@code value == 5 || value /= 5} is read at both leaves and joins to every
     * value there is. That is the same reconstruction {@code Predicates.Assumed} keeps a field of
     * its own to avoid, and the one this accounting was written against.
     */
    record Reading(AdmissibleReading values, OrderedReading ordered, Terms terms,
                   Map<FactSubject, Type> byName, Alternatives alternatives)
            implements ClauseReading<StatedByClauses, Denotations> {

        /** What a binding under a clause is entered as, for a fold over this reading. The one
         *  answer there is, asked of the one place that gives it (ADR-0106). */
        ClauseScope<Denotations> scope() {
            return terms::inside;
        }

        @Override
        public StatedByClauses nothingSaid() {
            return top();
        }

        /**
         * What each language makes of one leaf, and where each of them took it in.
         *
         * <p>Which positions the leaf is about is the clause's own content and is read once here;
         * which of them a language managed is that language's, taken from what it produced at this
         * leaf and nowhere else. A leaf about a position that a language has no word for is one it
         * missed, and the other language answering for it is what makes them two accounts rather
         * than one.
         */
        @Override
        public StatedByClauses leaf(Core e, boolean positive, Denotations at) {
            souther.compiler.values.PlannedValues<FactSubject> said = values.leaf(e, positive, at);
            OrderedIntervals<FactSubject> range = ordered.leaf(e, positive, at);
            Set<FactSubject> mentions = mentioned(e, at);
            return new Said(said, range,
                    // Each language says whether it gave up on the leaf. The reading of values
                    // carries it; the reading of order has nothing to hand back but its ranges, and
                    // a leaf it read leaves at least one.
                    Adoption.at(mentions, said.adoptedAt(), said.dropped()),
                    Adoption.at(mentions, range.ranges().keySet(), range.ranges().isEmpty()),
                    // And what the leaf states about the strings at a position, where it is a rule
                    // about them. Asked of the reading that recognises one, so this is where the
                    // answer enters and the connectives below are what compose it.
                    values.stringRuleIn(e, said, at),
                    Map.of());
        }

        /**
         * The positions of this value that {@code e} names.
         *
         * <p>A fact about the clause and not about either language, which is why it is read here
         * and once. A position names itself, and nothing under it is a position of its own.
         */
        private Set<FactSubject> mentioned(Core e, Denotations at) {
            Set<FactSubject> found = new LinkedHashSet<>();
            gather(e, found, at);
            return found;
        }

        private void gather(Core e, Set<FactSubject> found, Denotations at) {
            // Crossed as a binding, for the reason {@code AdmissibleReading.gather} gives.
            if (e instanceof Core.LetIn li) {
                gather(li.body(), found, terms.inside(li, at));
                return;
            }
            FactSubject here = terms.subjectOf(e, at);
            if (here != null && byName.containsKey(here)) {
                found.add(here);
                return;
            }
            Core.forEachChild(e, child -> gather(child, found, at));
        }

        @Override
        public StatedByClauses both(StatedByClauses one, StatedByClauses other) {
            return met(one, other);
        }

        /**
         * Both holding at once, distributed over a choice this could not settle.
         *
         * <p>A conjunction of a choice is the choice between the conjunctions. Merged into one
         * first, the reading would be answering about a branch that may not be there.
         *
         * <p>Reachable only through the fold that reads one clause, which is what keeps this tree
         * one rule's: the conjunction across rules has no operation here to arrive by, and is
         * written where the rules of a declaration meet ({@link StatedTogether#meet}).
         */
        private static StatedByClauses met(StatedByClauses one, StatedByClauses other) {
            if (one instanceof Choice it) {
                return new Choice(it.id(), met(it.left(), other), met(it.right(), other));
            }
            if (other instanceof Choice it) {
                return new Choice(it.id(), met(one, it.left()), met(one, it.right()));
            }
            Said here = (Said) one;
            Said there = (Said) other;
            return new Said(here.values().meet(there.values()),
                    here.ordered().meet(there.ordered()),
                    here.byValues().both(there.byValues()), here.byOrder().both(there.byOrder()),
                    StringRestriction.over(here.strings(), there.strings(), true),
                    // The parts of both, since a conjunction is every clause of it holding at once
                    // and each of them is still the part it was.
                    bothParts(here.parts(), there.parts()));
        }

        /**
         * What was read, remembering that it is what {@code e} came to.
         *
         * <p>Kept in the reading so that the branch rules below reach it. A part is answered
         * differently in a branch that stands and in one nobody can be in, and which of those it
         * turned out to be is settled by every clause of the value together.
         */
        @Override
        public StatedByClauses from(Core e, StatedByClauses out) {
            return out.from(e);
        }

        /**
         * Either alternative holding, an alternative that admits nothing being one nobody can take.
         *
         * <p>Asked of the pair and not of each language, which is the whole point of reading them
         * together.
         *
         * <p><b>Every alternative impossible is not one alternative impossible.</b> Where one of
         * them cannot be taken, the answer is the other and the first one's evidence goes with it —
         * nothing satisfies it, so what it said narrows nothing a value of this type is under, its
         * unread rules included. Where <em>all</em> of them cannot be taken, no one of them speaks
         * for the rest: taking the first to be found impossible out of the answer would settle the
         * proof by the order the operands were written in, and the same model written two ways would
         * be refused two ways.
         *
         * <p>Nor may they be met. A meet is a conjunction and the alternatives were never stated
         * together: {@code (a < "" && b == 0) || (a < "" && b == 1)} is impossible because of
         * {@code a}, and met it is a {@code b} bounded at 0 and at 1 — a contradiction neither
         * alternative contains, at a position the rules are fine with, and one the refusal would
         * then be written about.
         *
         * <p>So each side is taken as leaving nothing ({@link AdmissibleValues#leavingNothing},
         * {@link OrderedIntervals#leavingNothing}) and the languages are joined as they are for any
         * other choice. What each of them says the choice leaves empty is what <em>every</em>
         * alternative leaves empty, and where that is no position, the choice admits nothing with
         * none of them at fault. That is the rule {@link Emptiness.AcrossEveryCase} states for a
         * sum — what proves it has none is the whole list — arrived at here for the same reason.
         */
        @Override
        public StatedByClauses either(StatedByClauses one, StatedByClauses other) {
            if (one instanceof Said here && other instanceof Said there) {
                Emptiness a = here.emptiness();
                Emptiness b = there.emptiness();
                // A branch the descriptions already show empty is decided here whichever way the
                // declaration holds its choices. The answer is definitive — a description empty
                // before anything is built admits nothing however the other clauses refine it —
                // and a clause written later can only show more branches impossible, never fewer,
                // so nothing a deferral waits for can reach a different decision. Deferred anyway,
                // the dead branch would widen the met-together tree for nothing.
                if (a == Emptiness.EMPTY && b == Emptiness.EMPTY) {
                    return bothDead(here, there);
                }
                if (a == Emptiness.EMPTY) {
                    return beside(there, here);
                }
                if (b == Emptiness.EMPTY) {
                    return beside(here, there);
                }
                // Two live branches are another matter: merging them is the one decision a clause
                // written later can be too late for, since it is the branch structure the later
                // clause's conjunction would have refined. Held apart, the choice is held open past
                // the clause and settled by the rules of every clause together; the expansion the
                // deferral costs was counted over the whole declaration before any clause was
                // read, which is what admitted the declaration as APART at all.
                if (alternatives == Alternatives.MERGED
                        && a == Emptiness.NONEMPTY && b == Emptiness.NONEMPTY) {
                    return live(here, there);
                }
            }
            // And where whether a branch can be taken is not settled, the question waits — the
            // whole of it, and not the values alone. Which of the four above this comes to decides
            // what the positions admit, where they stop, and what each language is recorded as
            // having taken in; settled for some of those and held open for the rest, a branch that
            // turned out dead would have left an account of what it adopted behind it.
            return new Choice(new ChoiceId(), one, other);
        }

        /**
         * The met-together reading worked out, with the fate of every branch beside it.
         *
         * <p>Once, and this is where every choice is answered — over branches that are readings
         * rather than descriptions of them, by the same four rules a settled reading always used.
         * What comes back is a value: nothing downstream is left holding a decision, and nothing
         * recomputes one — the accounts ({@link #accountOf}) read the fates out of it.
         *
         * <p>A fate is aggregated over every place distribution put the branch — the reasoning is
         * {@link Settlement}'s. What is decided here per place is the emptiness of that occurrence,
         * and the join over occurrences is associative, commutative and idempotent, so the answer
         * cannot turn on the order the clauses were met in.
         */
        Settlement settle(StatedTogether read,
                          souther.compiler.values.Allowance<FactSubject> by) {
            Map<ChoiceId, Settlement.OfAChoice> outcomes = new java.util.LinkedHashMap<>();
            StatedTogether.Said said = settling(read, by, outcomes);
            return new Settlement(said.values().resolve(by), said.ordered(), outcomes);
        }

        /** The same reading with every choice in it decided, each occurrence noting its fate. */
        private StatedTogether.Said settling(StatedTogether read,
                                             souther.compiler.values.Allowance<FactSubject> by,
                                             Map<ChoiceId, Settlement.OfAChoice> outcomes) {
            return switch (read) {
                case StatedTogether.Said it -> it;
                case StatedTogether.Choice it -> {
                    StatedTogether.Said one = settling(it.left(), by, outcomes);
                    StatedTogether.Said other = settling(it.right(), by, outcomes);
                    Settlement.Sided here = probed(one, by);
                    Settlement.Sided there = probed(other, by);
                    outcomes.merge(it.id(), new Settlement.OfAChoice(here, there),
                            Settlement.OfAChoice::alsoSeen);
                    yield decided(one, here, other, there);
                }
            };
        }

        /**
         * What one occurrence of a choice leaves the values, by the rule its two fates pick.
         *
         * <p>The four rules of a settled reading, over the values and the ranges alone: what each
         * language recorded as taken in is the account's, answered over the rule's own tree with
         * the aggregated fates, and is not here to be answered per occurrence.
         */
        private StatedTogether.Said decided(StatedTogether.Said one, Settlement.Sided here,
                                            StatedTogether.Said other, Settlement.Sided there) {
            if (here.emptiness() == Emptiness.EMPTY && there.emptiness() == Emptiness.EMPTY) {
                // The rule for a choice nobody can take, named rather than arrived at: a join is
                // what two branches somebody can take come to, and neither of these is one.
                return new StatedTogether.Said(
                        one.values().leavingNothing().bothDead(other.values().leavingNothing()),
                        ordered.either(one.ordered().leavingNothing(),
                                other.ordered().leavingNothing()));
            }
            if (here.emptiness() == Emptiness.EMPTY) {
                return keptTogether(other, there);
            }
            if (there.emptiness() == Emptiness.EMPTY) {
                return keptTogether(one, here);
            }
            StatedTogether.Said left = keptTogether(one, here);
            StatedTogether.Said right = keptTogether(other, there);
            return new StatedTogether.Said(values.either(left.values(), right.values()),
                    ordered.either(left.ordered(), right.ordered()));
        }

        /**
         * A branch that is being kept, holding what working it out could not build.
         *
         * <p>A branch shown to admit something is kept and there is nothing more to say; a branch
         * nothing could work out is kept for the same reason nothing was dropped — nobody showed it
         * empty — and that is not the same fact. Kept without saying so, the reading would call a
         * position open where the truth is that nobody looked.
         */
        private StatedTogether.Said keptTogether(StatedTogether.Said read,
                                                 Settlement.Sided known) {
            if (known.emptiness() != Emptiness.UNDECIDED) {
                return read;
            }
            return new StatedTogether.Said(read.values().alsoStanding(known.standing()),
                    read.ordered());
        }

        /**
         * Whether anything satisfies a branch, asked of this occurrence of it worked out.
         *
         * <p>Three answers. A branch whose ordering admits nothing, or whose values came out empty,
         * is one nobody can be in here; a branch every position of which was worked out and which
         * admits something is one somebody can be in; and a branch with a position this compiler
         * could not build is neither, whatever the widened set it came back with says — and what
         * could not be built comes back with the answer, so a branch kept on it is kept saying so.
         *
         * <p>What the descriptions settle is settled before anything is built: a branch shown to
         * admit nothing, or to admit something, is decided without a machine, and only where the
         * descriptions leave the question open is the branch worked out to answer it.
         */
        private Settlement.Sided probed(StatedTogether.Said read,
                                        souther.compiler.values.Allowance<FactSubject> by) {
            Emptiness said = read.admits();
            if (said != Emptiness.UNDECIDED) {
                return Settlement.Sided.settledAs(said);
            }
            souther.compiler.values.Realized<FactSubject> made = read.values().resolve(by);
            // Worked out, the sets can be asked where the positions stop — which is the same
            // question as above and a different answer, the descriptions having become sets.
            Emptiness worked = new Confinement.OfAConjunction<>(
                    souther.compiler.values.ConjoinedAdmissibleValues.of(made.values(), by),
                    read.ordered(), ordered.carriers()).admits();
            if (worked == Emptiness.EMPTY) {
                return Settlement.Sided.settledAs(Emptiness.EMPTY);
            }
            // And a branch every position of which was worked out and which admits something is one
            // somebody can be in. A position nobody built is neither: what stands there is every
            // value, which is wider than the rules, so the branch may hold something they refuse.
            if (worked == Emptiness.NONEMPTY && made.unbuilt().isEmpty()) {
                return Settlement.Sided.settledAs(Emptiness.NONEMPTY);
            }
            Map<FactSubject, java.util.List<souther.compiler.values.UnreadReason>> why =
                    new java.util.LinkedHashMap<>(made.aboutARule());
            made.aboutTheAnswer().forEach(why::putIfAbsent);
            return new Settlement.Sided(Emptiness.UNDECIDED, why, made.unbuilt());
        }

        /**
         * What one rule's clauses took in, answered over that rule's own tree.
         *
         * <p>The one thing taken from outside the rule is the fate of its choices, which is the
         * whole declaration's to say and arrives settled ({@link Settlement}). Everything else —
         * what each part adopted, what stopped this reading of it — was recorded as the rule was
         * read, so nothing here builds a machine and nothing here can be widened by a constraint a
         * neighbouring rule stated: no neighbouring rule is in the tree.
         */
        Account accountOf(StatedByClauses rule, Settlement made,
                          souther.compiler.values.Allowance<FactSubject> by) {
            return new Account(narrowedBy(rule.alone(alternatives, by).values(), by),
                    partsOf(accounted(rule, made.outcomes()), made));
        }

        /**
         * The positions the rule itself holds to less than every value.
         *
         * <p>Off the rule settled on its own and not off the declaration's answer, because that one
         * is met from every rule that reached the position: read there, a rule that holds nothing
         * down is handed whatever its neighbours held down.
         *
         * <p><b>And settled, rather than composed and left at that.</b> A choice is decided by
         * whether anything satisfies each branch, which for a language is not known until the
         * machine exists — {@code (String.matches("A", t) && String.matches("B", t)) ||
         * String.matches("C", s)} holds {@code s} to one string, because nothing is both {@code "A"}
         * and {@code "B"} and the branch asking for both is one nobody can take. Joined without
         * deciding, the two branches leave {@code s} at every value and the rule looks like one that
         * states nothing.
         *
         * <p>Its own fates and not the declaration's, which is the whole of the distinction. A
         * branch this rule's own clauses rule out is this rule's work and belongs to what it did; a
         * branch that stands until a neighbour refuses it is the neighbour's, and lending it here is
         * how a rule that states nothing came to be reported as holding a position down.
         *
         * <p>Read against what was built and never by building. A pattern is a name for a machine
         * until one exists, so a format admitting every string and one admitting some read alike on
         * a description — and the position's answer, which was built, is where that is told apart.
         * Where nothing built it, this says nothing: a position the answer never worked out is not
         * one a rule can be said to have narrowed.
         */
        private Set<FactSubject> narrowedBy(
                souther.compiler.values.PlannedValues<FactSubject> mine,
                souther.compiler.values.Allowance<FactSubject> by) {
            Set<FactSubject> out = new java.util.LinkedHashSet<>();
            for (FactSubject each : mine.adoptedAt()) {
                souther.compiler.values.ValueSet known = by.known(each, mine.at(each));
                if (known != null && !known.isAny() && !known.isEmpty()) {
                    out.add(each);
                }
            }
            return out;
        }

        private Map<Core, PartAccount> partsOf(Said said, Settlement made) {
            Set<FactSubject> unbuilt = made.made().unbuilt();
            // And what could not be built is given up on here too. What a leaf said it adopted was
            // said before any machine was made, so a position whose answer the whole reading did
            // not work out is one the account still calls taken in — while the values beside it
            // say it holds every value because nobody worked it out.
            Map<Core, PartAccount> parts = new java.util.IdentityHashMap<>();
            said.parts().forEach((each, part) -> parts.put(each, new PartAccount(
                    part.byValues().unbuiltAt(unbuilt),
                    part.byOrder().unbuiltAt(unbuilt),
                    aRuleIsAnswerableFor(part, made.made()),
                    part.aboutStrings())));
            return parts;
        }

        /** The same rule's reading with every choice in it decided, by the fates alone. */
        private Said accounted(StatedByClauses read,
                               Map<ChoiceId, Settlement.OfAChoice> outcomes) {
            return switch (read) {
                case Said it -> it;
                case Choice it -> {
                    Said one = accounted(it.left(), outcomes);
                    Said other = accounted(it.right(), outcomes);
                    Settlement.OfAChoice fate = outcomes.get(it.id());
                    if (fate == null) {
                        // Every choice of a rule stands somewhere in the met-together reading, so
                        // a fate nobody settled is this compiler's arithmetic gone wrong and not a
                        // fact about any model.
                        throw new IllegalStateException(
                                "a choice of a rule was never met in the settled reading");
                    }
                    Emptiness here = fate.left().emptiness();
                    Emptiness there = fate.right().emptiness();
                    if (here == Emptiness.EMPTY && there == Emptiness.EMPTY) {
                        yield bothDead(one, other);
                    }
                    if (here == Emptiness.EMPTY) {
                        yield beside(keptAs(other, fate.right()), one);
                    }
                    if (there == Emptiness.EMPTY) {
                        yield beside(keptAs(one, fate.left()), other);
                    }
                    yield live(keptAs(one, fate.left()), keptAs(other, fate.right()));
                }
            };
        }

        /**
         * A branch of the rule that is being kept, holding what the settlement could not build in
         * it.
         *
         * <p>{@link #keptTogether} for the account: the reasons and the given-up positions were
         * settled where the branch's occurrences were probed, and are applied to what this rule's
         * parts said — a part about a position nobody worked out is one the account still calls
         * taken in until this is applied.
         */
        private Said keptAs(Said read, Settlement.Sided known) {
            if (known.emptiness() != Emptiness.UNDECIDED) {
                return read;
            }
            Map<Core, Part> parts = new java.util.IdentityHashMap<>();
            read.parts().forEach((each, part) -> parts.put(each, new Part(
                    part.byValues().unbuiltAt(known.unbuilt()),
                    part.byOrder().unbuiltAt(known.unbuilt()),
                    ReadByClauses.alsoSaying(part.standing(), known.standing()),
                    part.aboutStrings())));
            return new Said(read.values().alsoStanding(known.standing()), read.ordered(),
                    read.byValues().unbuiltAt(known.unbuilt()),
                    read.byOrder().unbuiltAt(known.unbuilt()),
                    read.strings(),
                    parts);
        }

        /**
         * What a rule of one part is answerable for: what its own reading wrote down, and what
         * working the answer out could not build at a position that part is about.
         *
         * <p>The second half is a projection and is said as one. Which rule a machine that was too
         * large belonged to is not something the working-out records — a position's answer is met
         * out of every rule that reached it — so what is honest is that a part naming the position
         * is a part the shortfall is about. A part naming no position it happened at is told
         * nothing.
         */
        private Map<FactSubject, java.util.List<souther.compiler.values.UnreadReason>>
                aRuleIsAnswerableFor(Part part, souther.compiler.values.Realized<FactSubject> made) {
            Map<FactSubject, java.util.List<souther.compiler.values.UnreadReason>> out =
                    new java.util.LinkedHashMap<>();
            part.standing().forEach((position, why) -> {
                java.util.List<souther.compiler.values.UnreadReason> mine = why.stream()
                        .filter(each -> each.about()
                                == souther.compiler.values.UnreadReason.About.A_RULE)
                        .toList();
                if (!mine.isEmpty()) {
                    out.put(position, mine);
                }
            });
            made.aboutARule().forEach((position, why) -> {
                if (part.byValues().mentions().contains(position)
                        || part.byOrder().mentions().contains(position)) {
                    out.merge(position, why, ReadByClauses::alsoSaying);
                }
            });
            return out;
        }

        /**
         * A choice neither branch of which anybody can take.
         *
         * <p>No one of them speaks for the rest: taking the first to be found impossible out of the
         * answer would settle the proof by the order the operands were written in, and the same
         * model written two ways would be refused two ways. So each side is taken as leaving
         * nothing and the languages are joined as they are for any other choice — what each of them
         * says the choice leaves empty is what <em>every</em> alternative leaves empty.
         */
        private Said bothDead(Said here, Said there) {
            return new Said(
                    // The rule for a choice nobody can take, named rather than arrived at: a join
                    // is what two branches somebody can take come to, and neither of these is one.
                    here.values().leavingNothing()
                            .bothDead(there.values().leavingNothing()),
                    ordered.either(here.ordered().leavingNothing(),
                            there.ordered().leavingNothing()),
                    here.byValues().bothDead(there.byValues()),
                    here.byOrder().bothDead(there.byOrder()),
                    // And what either of them said about the strings goes with them. A run drawn
                    // from a branch nobody can take is a line the model does not draw.
                    Map.of(),
                    branchParts(here.parts(), there.parts(), Part::bothDead,
                            Part::inADeadBranch));
        }

        /**
         * A choice one branch of which nobody can take, which is the other branch.
         *
         * <p>What the dead one said goes with it, its unread rules included: nothing satisfies it,
         * so what it left a position is not something a value of this type is under. What it does
         * leave is that the positions it named are settled — the choice does nothing to them — and
         * that is an answer only a reading that got to the end of the branch could give.
         */
        private Said beside(Said alive, Said gone) {
            return new Said(alive.values(), alive.ordered(),
                    alive.byValues().beside(gone.byValues()),
                    alive.byOrder().beside(gone.byOrder()),
                    // The branch that stands, and what the other could not read is not its
                    // business: a rule of a branch nothing satisfies hides no run of this one.
                    alive.strings(),
                    branchParts(alive.parts(), gone.parts(), Part::beside,
                            Part::inADeadBranch));
        }

        /** A choice both branches of which somebody can take. */
        private Said live(Said here, Said there) {
            return new Said(values.either(here.values(), there.values()),
                    ordered.either(here.ordered(), there.ordered()),
                    here.byValues().either(there.byValues()),
                    here.byOrder().either(there.byOrder()),
                    StringRestriction.over(here.strings(), there.strings(), false),
                    branchParts(here.parts(), there.parts(), Part::either,
                            java.util.function.UnaryOperator.identity()));
        }
    }

    /** The parts of two readings held together, each of them still the part it was. */
    private static Map<Core, Part> bothParts(Map<Core, Part> these, Map<Core, Part> those) {
        if (those.isEmpty()) {
            return these;
        }
        Map<Core, Part> out = new java.util.IdentityHashMap<>(these);
        out.putAll(those);
        return out;
    }

    /**
     * The parts of the two branches of a choice, put together the way the choice was.
     *
     * <p><b>Every part by the same rule the whole was.</b> A node inside one branch is only that
     * branch's, and is answered by what happened to the branch. A node above the choice — the
     * clause itself, and every conjunct the reading distributed into both — is in each of them, and
     * what it comes to is the two accounts put together by the rule that decided the choice. Taking
     * one side's copy instead, a clause that mentions a position only in the branch that died came
     * back saying nothing about it, and a question stood at a position of a branch nobody can be in.
     *
     * @param whole what one part of each side comes to, which is the choice's own rule
     * @param alone what a part on one side alone comes to, since it is inside that branch
     */
    private static Map<Core, Part> branchParts(Map<Core, Part> here, Map<Core, Part> there,
                                               java.util.function.BinaryOperator<Part> whole,
                                               java.util.function.UnaryOperator<Part> alone) {
        Map<Core, Part> out = new java.util.IdentityHashMap<>();
        here.forEach((each, part) -> {
            Part beside = there.get(each);
            out.put(each, beside == null ? alone.apply(part) : whole.apply(part, beside));
        });
        there.forEach((each, part) -> {
            if (!here.containsKey(each)) {
                out.put(each, alone.apply(part));
            }
        });
        return out;
    }

    /**
     * The clauses of one value as they were read, and every part of them, waiting to be worked out.
     *
     * <p>Held rather than asked. What a clause adopted, and what each part of it adopted, turn on
     * which branch of a choice anybody can be in — and that is not known until the machines are
     * made. Asked as each clause was read, the account answered from what the reading happened to
     * hold, and a rule of a branch nothing satisfies was written down as a rule of this declaration
     * that went unanswered.
     *
     * <p><b>And worked out together, once.</b> Everything here is the same declaration's answer and
     * draws on the same allowance, so the order they are worked out in is the order it is spent in.
     * Kept in the order the clauses were read and the parts were reached: a walk over a table keyed
     * by what a node happens to be would make what a declaration can be told exactly turn on where
     * its clauses landed in it.
     *
     * @param <K> what a caller files each clause under
     */
    final class Asked<K> {

        private final Map<K, Core> byClause = new java.util.LinkedHashMap<>();
        private final Map<K, java.util.List<Core>> byPart = new java.util.LinkedHashMap<>();
        private final Map<K, StatedByClauses> trees = new java.util.LinkedHashMap<>();

        /** One clause read from {@code at}, with the parts of it noted in the order the reading
         *  reached them. */
        StatedByClauses read(Reading reader, Denotations at, K key, Core clause) {
            java.util.List<Core> parts = new java.util.ArrayList<>();
            StatedByClauses one = reader.read(clause, true, at, reader.scope(),
                    (part, _) -> parts.add(part));
            byClause.put(key, clause);
            byPart.put(key, parts);
            trees.put(key, one);
            return one;
        }

        /**
         * All of it worked out, once, and every rule of it answered over its own tree.
         *
         * <p>One settlement because there is one value: the clauses are met over
         * {@link StatedTogether}, in the order they were read, and everything that has to be built
         * is built there, under the one allowance, with the fate of every branch coming back as
         * part of the result. Each rule's account is then its own tree with those fates applied —
         * its own tree, because what a rule took in is a fact about its clauses and not about the
         * constraints its neighbours distributed beside them; and the fates, because a branch of it
         * nobody anywhere can be in is not a branch whose rules went unread. Nothing in the second
         * step builds a machine.
         */
        Answered<K> resolve(Reading reader, souther.compiler.values.Allowance<FactSubject> by,
                            souther.compiler.values.Allowance<FactSubject> handingOn) {
            StatedTogether whole = StatedTogether.top();
            for (StatedByClauses each : trees.values()) {
                whole = whole.meet(each.together());
            }
            Settlement made = reader.settle(whole, by);
            Map<Core, PartAccount> said = new IdentityHashMap<>();
            Map<K, Set<FactSubject>> narrowed = new LinkedHashMap<>();
            Adoption<FactSubject> byValues = Adoption.nothing();
            Adoption<FactSubject> byOrder = Adoption.nothing();
            // What the answer has left, before an account is made out of it. Every account below
            // reads what was built and builds nothing, so this is what it costs — and an account
            // that spent would be taking the budget the answer is bounded by to say which rule a
            // reason belongs to.
            //
            // Here rather than around the whole of this: the answer above is what the allowance is
            // for and spends it by design, so a check that started before it would be about
            // something else and would never fail.
            Map<FactSubject, Integer> unspent = leftOf(by, made.made().values().subjects());
            for (Map.Entry<K, StatedByClauses> each : trees.entrySet()) {
                // The rule on its own as well as in the declaration, because what it did to a
                // position and what the position came to are two questions. Its own choices are
                // decided by its own clauses against what the answer already established; met with
                // its neighbours first, a branch they refuse is dropped and the rule is credited
                // with a narrowing it did not do.
                Account mine = reader.accountOf(each.getValue(), made, by);
                said.putAll(mine.parts());
                PartAccount clause = mine.parts().get(byClause.get(each.getKey()));
                narrowed.put(each.getKey(), mine.narrowed());
                byValues = byValues.both(clause.byValues());
                byOrder = byOrder.both(clause.byOrder());
            }
            // An assertion because it is about this compiler and not about any model, and here
            // rather than in one test because every declaration a corpus holds goes through it.
            assert unspent.equals(leftOf(by, made.made().values().subjects()))
                    : "making the accounts of a declaration spent its allowance";
            // And here the reading stops being one and becomes an answer. What each rule about the
            // strings at a position leaves is worked out now, once, and a reader downstream is
            // handed the sets.
            //
            // Out of the allowance for handing rules on and not out of the answer's. The sets the
            // answer needed are met together and are already built; these are what each rule leaves
            // on its own, which the answer had no use for — charged to it, what a position is read
            // to admit would turn on what a reader downstream was promised, and the assertion above
            // would be true of the accounts and false of the reading as a whole.
            Map<Core, ReadByClauses.OfAPart> published =
                    published(said, handingOn, made.made().values());
            // And the answer's allowance is where it was. What a position admits is answered under
            // the allowance for it and nothing else reaches that allowance, so what this
            // declaration can be told exactly is the same whether or not anybody is ever handed
            // anything — which is the whole of why the sets handed on have an allowance of their
            // own.
            assert unspent.equals(leftOf(by, made.made().values().subjects()))
                    : "handing the rules of " + made.made().values().subjects()
                            + " on spent the allowance for what they admit";
            Map<K, ReadByClauses.OfARule> clauses = new LinkedHashMap<>();
            narrowed.forEach((key, these) -> clauses.put(key,
                    new ReadByClauses.OfARule(these, published.get(byClause.get(key)))));
            ReadByClauses read = new ReadByClauses(made.made().values(), made.ordered(),
                    byValues, byOrder, published);
            Map<K, java.util.List<Map.Entry<Core, ReadByClauses.OfAPart>>> parts =
                    new java.util.LinkedHashMap<>();
            byPart.forEach((key, these) -> {
                java.util.List<Map.Entry<Core, ReadByClauses.OfAPart>> out =
                        new java.util.ArrayList<>();
                these.forEach(each -> {
                    ReadByClauses.OfAPart one = published.get(each);
                    if (one != null) {
                        out.add(Map.entry(each, one));
                    }
                });
                parts.put(key, out);
            });
            return new Answered<>(read, clauses, parts);
        }

        /**
         * Every part with what it says about the strings worked out, position by position.
         *
         * <p><b>The whole of a position at once ({@link souther.compiler.values.Allowance
         * #realizeAll}).</b> What this reading promises a reader is what each of its parts admits,
         * and the promise is one thing: a position whose allowance cannot make every one of them
         * publishes none, so which rules a reader hears about is not decided by which plan the
         * building reached first. Made part by part, two rules of one position each affordable
         * alone would be published or not by the order this walk happened to take.
         *
         * <p>What was not read stays what was not read. A rule this compiler could not turn into a
         * set is a fact about the rule and was settled long before anything was built, so it
         * crosses unchanged — it is not a set nobody made, and a reader that met it as one would be
         * told the position's allowance ran out on a rule nothing ever asked to be built.
         *
         * <p>What the answer built is read and not built again ({@link Allowance#besides}). A rule
         * that stands alone at a position is the position's answer, and its machine exists by the
         * time this asks — so what is charged to the allowance for handing rules on is what the
         * answer had no use for, which is what that allowance is for.
         *
         * <p><b>And nothing is published at a position the answer does not speak for.</b> What each
         * rule leaves is a projection of what the position admits, and a projection may not answer
         * where the thing it projects could not: given its own allowance to try again, the reading
         * would be telling a reader which strings a rule leaves at a position it has just said it
         * cannot say what stands at, and the two would differ over exactly the patterns one of them
         * can afford — which is the arrangement this whole reading exists to remove. So the second
         * allowance makes up what the first had no use for, and never what it could not manage.
         *
         * <p>Whether a position was answered exactly is asked of the answer
         * ({@link AdmissibleValues#speaksFor}) and worked out from nothing here. A rule left
         * standing at a position is one of the things that question weighs and not the answer to
         * it: an alternative that covers the position leaves it exact with an unread rule beside
         * it, and a reading that read the reasons for itself would call such a position short of
         * something and publish nothing about it, under a word for an allowance nothing had spent.
         *
         * @param answered what the positions came to, asked whether each of them is exact
         */
        private Map<Core, ReadByClauses.OfAPart> published(
                Map<Core, PartAccount> said, Allowance<FactSubject> handingOn,
                AdmissibleValues<FactSubject> answered) {
            Map<FactSubject, Set<AdmittedPlan>> asked = new LinkedHashMap<>();
            said.values().forEach(part -> part.aboutStrings().forEach((position, stated) -> {
                if (stated instanceof StringRestriction.Admitting it) {
                    asked.computeIfAbsent(position, _ -> new LinkedHashSet<>()).add(it.plan());
                }
            }));
            Map<FactSubject, Realizations> answers = new LinkedHashMap<>();
            asked.forEach((position, plans) -> answers.put(position,
                    answered.speaksFor(position) ? handingOn.realizeAll(position, plans)
                            : new Realizations.NotBuilt()));
            Map<Core, ReadByClauses.OfAPart> out = new IdentityHashMap<>();
            said.forEach((each, part) -> out.put(each, new ReadByClauses.OfAPart(
                    part.byValues(), part.byOrder(), part.aboutARule(),
                    admitted(part.aboutStrings(), answers))));
            return out;
        }

        /**
         * What one part's rules about the strings came to, out of the answers the positions gave.
         *
         * <p>A rule of a position that did not publish keeps its place and is told that much and no
         * more. Which rules a clause states about the strings is what a walk over it asks, and an
         * entry dropped would be read as a clause that states none; a reason put here instead would
         * be the position's shortfall written out once per rule of it, over rules that may each
         * have been affordable.
         */
        private static Map<FactSubject, AdmittedStrings> admitted(
                Map<FactSubject, StringRestriction> stated,
                Map<FactSubject, Realizations> answers) {
            if (stated.isEmpty()) {
                return Map.of();
            }
            Map<FactSubject, AdmittedStrings> out = new LinkedHashMap<>();
            stated.forEach((position, said) -> {
                switch (said) {
                    case StringRestriction.NotKnown it ->
                            out.put(position, new AdmittedStrings.NotKnown(it.why()));
                    case StringRestriction.Admitting it ->
                            out.put(position, answers.get(position) instanceof Realizations.Exact made
                                    ? new AdmittedStrings.Admitting(made.of(it.plan()))
                                    : new AdmittedStrings.NotPublished());
                }
            });
            return Collections.unmodifiableMap(out);
        }
    }

    /**
     * What {@link Asked} came to: the whole, each clause, and each part of each clause.
     *
     * <p>The second and third are looked up in the first. Reading them any number of times spends
     * nothing, because the work was done once and what is here is what it came to.
     */
    record Answered<K>(ReadByClauses whole, Map<K, ReadByClauses.OfARule> perClause,
                       Map<K, java.util.List<Map.Entry<Core, ReadByClauses.OfAPart>>> perPart) {}

    /**
     * What one rule's own tree came to: what it leaves narrowed, and what each of its parts took in.
     *
     * <p>Both from one walk of the rule. Asked apart, the tree would be answered over twice and the
     * two answers agree only for as long as nobody changes one of them.
     */
    record Account(Set<FactSubject> narrowed, Map<Core, PartAccount> parts) {}

    /**
     * What one part came to, with what it says about the strings still named as a plan.
     *
     * <p>One step short of {@link ReadByClauses.OfAPart}, and the step is the only difference: the
     * rules about the strings at a position are still what would be built rather than what was.
     * They are made into sets once, for the whole position, where the reading publishes what it
     * read — so that the plans never reach a reader and the position pays for its own answer in one
     * place.
     */
    record PartAccount(Adoption<FactSubject> byValues, Adoption<FactSubject> byOrder,
                       Map<FactSubject,
                               java.util.List<souther.compiler.values.UnreadReason>> aboutARule,
                       Map<FactSubject, StringRestriction> aboutStrings) {}

    /** What the allowance has left at each of {@code positions}, for holding an account to
     *  spending nothing. */
    private static Map<FactSubject, Integer> leftOf(
            souther.compiler.values.Allowance<FactSubject> by, Set<FactSubject> positions) {
        Map<FactSubject, Integer> out = new java.util.LinkedHashMap<>();
        positions.forEach(each -> out.put(each, by.left(each)));
        return out;
    }
}
