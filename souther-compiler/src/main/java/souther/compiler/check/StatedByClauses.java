package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.types.Type;
import souther.compiler.values.AdmissibleValues;
import souther.compiler.values.Emptiness;

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * What the clauses of one value say, in each of the languages a clause is read in.
 *
 * <p>Two languages and one reading. Which values a position may take is a set, and where a position
 * stops is a range, and neither says what the other says — an ordering names no finite set, and a
 * set of values has no word for what lies between two of them. So a clause reaches whichever of them
 * has a word for it, and some clauses reach both.
 *
 * <p><b>The connectives are over this and not over either of them.</b> A choice between two
 * alternatives is a choice between two readings of the whole value, so an alternative that cannot be
 * taken is dropped by asking the whole of what is known about it ({@link #holdsNothing}). Applied
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
                Adoption<FactSubject> byValues, Adoption<FactSubject> byOrder)
            implements StatedByClauses {}

    /**
     * A choice whose branches this cannot tell apart yet.
     *
     * <p>An interpreted connective and not an unread one: the clause said {@code ||} and this is
     * what {@code ||} means, held open only because whether either branch admits anything turns on
     * machines nobody has made.
     *
     * <p><b>The whole of what was read, and not its values alone.</b> A branch is dropped, kept, or
     * kept beside a dead one, and every part of a reading is answered differently by each of those
     * — what the positions admit, where they stop, and which rules each language took in. Held open
     * for the values while the rest was settled, a branch that turned out dead left its adoption
     * behind: the account said a rule of a branch nothing satisfies had gone unread, and there was
     * no branch for an author to go and look at.
     */
    record Choice(StatedByClauses left, StatedByClauses right) implements StatedByClauses {

        public Choice {
            if (left == null || right == null) {
                throw new IllegalArgumentException("a choice is between two readings");
            }
        }
    }

    /** Nothing read, so nothing ruled out. */
    static StatedByClauses top() {
        return new Said(souther.compiler.values.PlannedValues.top(),
                OrderedIntervals.top(),
                Adoption.nothing(), Adoption.nothing());
    }

    /**
     * Whether anything satisfies what has been read, as far as that is settled.
     *
     * <p>Either language, because each can hold the whole answer on its own: what one of them
     * cannot express it leaves alone. Where a language is settled that nothing satisfies it, that
     * is the answer; where the values are a description nobody has built, the answer waits.
     */
    default Emptiness emptiness() {
        return switch (this) {
            case Choice it -> it.left().emptiness().joined(it.right().emptiness());
            case Said it -> it.ordered().isBottom() ? Emptiness.EMPTY : it.values().emptiness();
        };
    }

    /**
     * Both holding at once, distributed over a choice this could not settle.
     *
     * <p>A conjunction of a choice is the choice between the conjunctions. Merged into one first,
     * the reading would be answering about a branch that may not be there.
     */
    default StatedByClauses meet(StatedByClauses other) {
        if (this instanceof Choice it) {
            return new Choice(it.left().meet(other), it.right().meet(other));
        }
        if (other instanceof Choice it) {
            return new Choice(meet(it.left()), meet(it.right()));
        }
        Said here = (Said) this;
        Said there = (Said) other;
        return new Said(here.values().meet(there.values()),
                here.ordered().meet(there.ordered()),
                here.byValues().both(there.byValues()), here.byOrder().both(there.byOrder()));
    }

    /** The reading of one value's positions, made once and used over however many clauses reach it.
     *  Built per clause, this walk paid for a pair of readers at every clause of every value. */
    static Reading readingOf(Terms terms, Denotations at, Map<FactSubject, Type> byName,
                             Symbols symbols, Alternatives alternatives,
                             souther.compiler.values.Allowance<FactSubject> allowed) {
        return new Reading(AdmissibleReading.of(terms, at, byName, symbols, alternatives, allowed),
                OrderedReading.of(terms, at, byName, symbols), terms, at, byName);
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
    record Reading(AdmissibleReading values, OrderedReading ordered, Terms terms, Denotations at,
                   Map<FactSubject, Type> byName)
            implements ClauseReading<StatedByClauses> {

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
        public StatedByClauses leaf(Core e, boolean positive) {
            souther.compiler.values.PlannedValues<FactSubject> said = values.leaf(e, positive);
            OrderedIntervals<FactSubject> range = ordered.leaf(e, positive);
            Set<FactSubject> mentions = mentioned(e);
            return new Said(said, range,
                    // Each language says whether it gave up on the leaf. The reading of values
                    // carries it; the reading of order has nothing to hand back but its ranges, and
                    // a leaf it read leaves at least one.
                    Adoption.at(mentions, said.adoptedAt(), said.dropped()),
                    Adoption.at(mentions, range.ranges().keySet(), range.ranges().isEmpty()));
        }

        /**
         * The positions of this value that {@code e} names.
         *
         * <p>A fact about the clause and not about either language, which is why it is read here
         * and once. A position names itself, and nothing under it is a position of its own.
         */
        private Set<FactSubject> mentioned(Core e) {
            Set<FactSubject> found = new LinkedHashSet<>();
            gather(e, found);
            return found;
        }

        private void gather(Core e, Set<FactSubject> found) {
            FactSubject here = terms.subjectOf(e, at);
            if (here != null && byName.containsKey(here)) {
                found.add(here);
                return;
            }
            Core.forEachChild(e, child -> gather(child, found));
        }

        @Override
        public StatedByClauses both(StatedByClauses one, StatedByClauses other) {
            return one.meet(other);
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
                if (a == Emptiness.EMPTY && b == Emptiness.EMPTY) {
                    return bothDead(here, there);
                }
                if (a == Emptiness.EMPTY) {
                    return beside(there, here);
                }
                if (b == Emptiness.EMPTY) {
                    return beside(here, there);
                }
                if (a == Emptiness.NONEMPTY && b == Emptiness.NONEMPTY) {
                    return live(here, there);
                }
            }
            // And where whether a branch can be taken is not settled, the question waits — the
            // whole of it, and not the values alone. Which of the four above this comes to decides
            // what the positions admit, where they stop, and what each language is recorded as
            // having taken in; settled for some of those and held open for the rest, a branch that
            // turned out dead would have left an account of what it adopted behind it.
            return new Choice(one, other);
        }

        /**
         * What the choice comes to, with every branch of it worked out.
         *
         * <p>Where the question waited, this is where it is answered — once, by the rules above,
         * on branches that are readings rather than descriptions of them. Nothing downstream is
         * left holding a decision: what comes back has a set at every position, an account of what
         * each language took in, and no branch anybody still has to choose between.
         */
        ReadByClauses resolve(StatedByClauses read,
                              souther.compiler.values.Allowance<FactSubject> by) {
            Said said = settled(read, by);
            souther.compiler.values.Realized<FactSubject> made = said.values().resolve(by);
            // And what could not be built is given up on here too. What a leaf said it adopted was
            // said before any machine was made, so a position whose answer this did not work out is
            // one the account still calls taken in — while the values beside it say it holds every
            // value because nobody worked it out.
            return new ReadByClauses(made.values(), said.ordered(),
                    said.byValues().unbuiltAt(made.unbuilt()),
                    said.byOrder().unbuiltAt(made.unbuilt()));
        }

        /**
         * The same reading with every choice in it decided, which is one reading.
         *
         * <p>The branches are worked out to decide, and then the decision is made over the
         * descriptions rather than over what they came to: the four rules are the ones a settled
         * reading always used, and what they are applied to is the same two branches. Joined as the
         * worked-out readings instead, every position of the choice would be a machine made out of
         * sets that were already machines, which is work nobody described.
         */
        private Said settled(StatedByClauses read,
                             souther.compiler.values.Allowance<FactSubject> by) {
            return switch (read) {
                case Said it -> it;
                case Choice it -> {
                    Said one = settled(it.left(), by);
                    Said other = settled(it.right(), by);
                    souther.compiler.values.Emptiness here = emptinessOf(one, by);
                    souther.compiler.values.Emptiness there = emptinessOf(other, by);
                    if (here == Emptiness.EMPTY && there == Emptiness.EMPTY) {
                        yield bothDead(one, other);
                    }
                    // A branch this could not work out is one nothing showed empty, so it is kept
                    // — which is sound and is not exact. What is not sound is keeping it and
                    // dropping the reason: the branch beside it would be answered as though this
                    // one had been read, and the account would say a position it names is open
                    // where the truth is that nobody looked. So the shortfall goes with whichever
                    // branch survives, and the plan built afterwards cannot lose it by coming out
                    // a different shape.
                    if (here == Emptiness.EMPTY) {
                        yield beside(carrying(other, by), one);
                    }
                    if (there == Emptiness.EMPTY) {
                        yield beside(carrying(one, by), other);
                    }
                    yield live(carrying(one, by), carrying(other, by));
                }
            };
        }

        /**
         * Whether anything satisfies a branch, asked of the branch worked out.
         *
         * <p>Three answers. A branch whose ordering admits nothing, or whose values came out
         * empty, is one nobody can be in; a branch every position of which was worked out and which
         * admits something is one somebody can be in; and a branch with a position this compiler
         * could not build is neither, whatever the widened set it came back with says.
         */
        private Emptiness emptinessOf(Said read,
                                      souther.compiler.values.Allowance<FactSubject> by) {
            return read.ordered().isBottom() ? Emptiness.EMPTY : read.values().resolve(by)
                    .emptiness();
        }

        /** The same branch, holding what working it out could not build. */
        private Said carrying(Said read, souther.compiler.values.Allowance<FactSubject> by) {
            souther.compiler.values.Realized<FactSubject> made = read.values().resolve(by);
            if (made.unbuilt().isEmpty()) {
                return read;
            }
            java.util.Map<FactSubject, java.util.List<souther.compiler.values.UnreadReason>> why =
                    new java.util.LinkedHashMap<>(made.aboutARule());
            made.aboutTheAnswer().forEach(why::putIfAbsent);
            return new Said(read.values().alsoStanding(why), read.ordered(),
                    read.byValues().unbuiltAt(made.unbuilt()),
                    read.byOrder().unbuiltAt(made.unbuilt()));
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
                    here.byOrder().bothDead(there.byOrder()));
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
                    alive.byOrder().beside(gone.byOrder()));
        }

        /** A choice both branches of which somebody can take. */
        private Said live(Said here, Said there) {
            return new Said(values.either(here.values(), there.values()),
                    ordered.either(here.ordered(), there.ordered()),
                    here.byValues().either(there.byValues()),
                    here.byOrder().either(there.byOrder()));
        }
    }
}
