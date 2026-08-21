package souther.compiler.values;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BinaryOperator;

/**
 * Which values each position may hold, over all the rules a reading took in.
 *
 * <p>A state and not a set. A rule is written about a whole value and may name several of its
 * positions, and the connectives join whole readings rather than the answer at one position — so
 * what a conjunction and a disjunction are applied to is this, and the arithmetic at one position
 * is {@link ValueSet}.
 *
 * <h2>What is held</h2>
 *
 * <p>A union of products, or nothing. A product — a {@link Box} — is one set per position, standing
 * for every value with a value of each set at each place; a union of them is what a choice between
 * alternatives written at two positions leaves, and no one product holds it. How many of them a
 * reading may hold is what a caller bounds; held one at a time, the union is merged back into the
 * smallest box containing it, which is what a reading of these was before it held any.
 *
 * <p><b>Bottom is a state and not always a position.</b> The rules leave nothing where some position
 * is left no value — and also where every alternative of a choice is one nobody can take, which is
 * not a fact about any one position. So a reading that admits nothing is its own case
 * ({@link Held.Nothing}), and not an empty union: an empty union would say that no position can hold
 * anything, which is more than the rules were read to say.
 *
 * <p>What it carries is a {@link BottomResidue} — where the arithmetic had got to when it learned
 * that nothing satisfies the rules. Not the relation's projections, which are all empty once the
 * relation is: a position the residue holds values at is one the rules said something about, and it
 * is answered with rather than passed over so that a reader is told which position was left no
 * value and which was not.
 *
 * <p><b>A position no box holds is at {@link ValueSet#ANY}.</b> That is what makes the two
 * connectives what they are below, and it is the one thing to hold on to while reading them.
 *
 * <pre>
 *     meet             the keys of both, each side missing one standing at ANY
 *     join             the keys of both, each side missing one standing at ANY
 * </pre>
 *
 * <p>Which reads the same and is not: joining at a key one side does not hold is joining with ANY,
 * and that is ANY — so a join keeps only what both sides spoke about, and a meet keeps everything
 * either did. {@code value == "A" || something-this-cannot-read} has to come out saying nothing
 * about {@code value}, and a join written as a merge of the two maps says {@code "A"}.
 *
 * <h2>What the reading knows about itself</h2>
 *
 * <p>Beside the values, which positions this can speak for. A reading that could not take a rule in
 * leaves the values wider than the rules are, which is the safe direction for refusing a
 * declaration — nothing is admitted that the rules exclude — and the wrong direction for saying
 * that a model divides a position into these classes and no others. The two answers are different
 * questions and are kept apart: {@link #at} says which values, {@link #speaksFor} says whether that
 * is the whole of what the rules leave.
 *
 * <p>What a position holds is answered from two sides. {@link #at} is an upper approximation and
 * {@link #guaranteedAt} a lower one, and between them sits what the rules truly leave:
 *
 * <pre>
 *     guaranteedAt(p)   &#8838;   what is truly admitted at p   &#8838;   at(p)
 * </pre>
 *
 * <p>The lower one is what a choice needs. An alternative that admits every value at a position
 * settles it however little was read beside it, and a reading holding only "something went unread"
 * has thrown away what it would take to know that — which is why the two ends are carried and not
 * a flag standing for their difference.
 *
 * <p>Two things spoil it, and the second is the one that is easy to miss.
 *
 * <p>A rule this could not read spoils the positions it names, and what stopped it travels with
 * them ({@link UnreadReason}). It cannot spoil a position it does not name: nothing here relates
 * one position to another, so a rule that narrows a position names it — a rule relating two of them
 * names both, and is itself a rule this cannot read.
 *
 * <p>A rule this could not read spoils, under a disjunction, every position the other branch spoke
 * about, whether or not it names them. {@code value == "A" || opaque()} leaves {@code value} at ANY
 * because a value satisfying the second branch is under no obligation from the first — and ANY
 * arrived at that way is not the ANY of a position nothing was written about. Without this a
 * position would be reported as one the model draws no distinction at, when what happened is that
 * this reading could not follow the distinction the model draws.
 *
 * <p>Unless the alternatives already cover the position, which is the one thing that stops it.
 * {@code (value == "A" || value /= "A") || opaque()} leaves nothing for the unread branch to take
 * back: the two that were read admit every value between them, and a choice one of whose
 * alternatives admits every value at a position admits every value at it. That is what
 * {@link #guaranteedAt} is carried for, and holding "something went unread" alone would answer the
 * same clause two ways depending on where its brackets fell.
 */
public record AdmissibleValues<A>(Held<A> held, Map<A, UnreadReason> standing,
                                  boolean dropped,
                                  Map<A, ValueSet> guaranteed, ValueSet defaultGuaranteed,
                                  boolean guaranteedTogether,
                                  Set<A> tangled, Set<A> widened) {

    /**
     * What the rules a reading took in leave: some alternatives, or nothing at all.
     *
     * <p>The two are not one shape with a flag. Nothing is not an empty union — read as one, a
     * position would come out unable to hold anything, and what is known is about the whole value.
     * And a union of alternatives is never empty, so nothing is left to mean by an empty one.
     */
    public sealed interface Held<A> {

        /**
         * Nothing satisfies the rules, and what the arithmetic was holding when it found out.
         *
         * <p>The residue is not the relation's projections. Those are empty wherever the relation
         * is, and saying so at a position would name one the rules are fine with.
         */
        record Nothing<A>(BottomResidue<A> residue) implements Held<A> {}

        /**
         * The alternatives the rules leave, none of which admits nothing.
         *
         * <p>A set and not a sequence: what is held is their union, so the same alternative written
         * twice is one alternative and the order two of them were met in is not part of the answer.
         * Iterated in the order they were found all the same — what is written out of a reading has
         * to come out the same on two compiles of one model.
         */
        record Alternatives<A>(Set<Box<A>> boxes) implements Held<A> {
            public Alternatives {
                if (boxes.isEmpty()) {
                    throw new IllegalArgumentException("a reading holding no alternative is Nothing");
                }
                boxes = Collections.unmodifiableSet(new LinkedHashSet<>(boxes));
            }
        }
    }

    /**
     * One product: what each position may hold, with every combination of them standing.
     *
     * <p>A position at {@link ValueSet#ANY} is left out, so that what is held is what was said. No
     * position is left no value — a product with an empty side stands for nothing, which is not an
     * alternative but the absence of one, and telling them apart is {@link PairOutcome}'s.
     */
    public record Box<A>(Map<A, ValueSet> at) {
        public Box {
            at = said(at);
        }

        ValueSet get(A atom) {
            return at.getOrDefault(atom, ValueSet.ANY);
        }
    }

    /**
     * Where the arithmetic had got to when it learned that nothing satisfies the rules.
     *
     * <p>Evidence and not a relation. It holds positions left no value beside positions a rule
     * narrowed and left values at, and neither is a claim about what a value of this type may hold:
     * nothing may. What it is here for is that a reader asking which position was left nothing gets
     * the answer the reading had, rather than "every position" or "no position".
     *
     * <p><b>Nothing here says whether the reading is bottom.</b> That is {@link Held.Nothing}'s to
     * say, and a residue read for an empty set would answer it wrong: a reading shown to admit
     * nothing from outside carries no position at all, and its residue holds every value everywhere.
     */
    public record BottomResidue<A>(Map<A, ValueSet> at) {
        public BottomResidue {
            at = said(at);
        }

        ValueSet get(A atom) {
            return at.getOrDefault(atom, ValueSet.ANY);
        }
    }

    /**
     * What one product of two alternatives came to: an alternative, or the absence of one.
     *
     * <p>The one place a set of values per position is asked whether anything stands in it. Written
     * anywhere else, a map that happens to hold no position reads as the product of nothing, which
     * is every value at every position — so a reading shown to admit nothing would come back as one
     * admitting everything.
     */
    public sealed interface PairOutcome<A> {

        record Live<A>(Box<A> box) implements PairOutcome<A> {}

        record Dead<A>(BottomResidue<A> residue) implements PairOutcome<A> {}

        static <A> PairOutcome<A> of(Map<A, ValueSet> at) {
            return at.values().stream().anyMatch(ValueSet::isEmpty)
                    ? new Dead<>(new BottomResidue<>(at)) : new Live<>(new Box<>(at));
        }
    }

    /**
     * @param held what the rules leave: the alternatives, or nothing
     * @param standing what a rule left standing at each position, and what stopped the reading
     *                from taking it in. Why and not only which: two of these are lifted by
     *                different work and reported differently, and a reader handed the positions
     *                alone would have to go back to the rules to find out which it was.
     *
     *                <p><b>Not the positions this cannot speak for.</b> A rule left standing where
     *                the alternatives cover the position between them is one nothing there is
     *                answerable for, and it is held all the same, since whether they still cover it
     *                turns on rules stated beside the choice that have not been read yet.
     *                {@link #speaksFor} and {@link #whyUnread} are the readings; this is what they
     *                are read from
     * @param dropped whether a rule was left unread anywhere in this reading, which is what a
     *                disjunction needs in order to know that a branch widened it. What stopped that
     *                rule is not carried: a position the other branch spoke about is spoiled by
     *                there having been an alternative it could not read, and not by whatever the
     *                rule in that alternative was about
     * @param guaranteed which values each position is guaranteed to admit — read through
     *                {@link #guaranteedAt} rather than off this map, which holds a position whose
     *                guarantee is the default as well. Held that way on purpose: the keys are
     *                {@link #promisedAt}, the positions a rule of this reading reached, and
     *                dropping the ones that came to the default would make that set turn on which
     *                rules happened to leave a position where it started. A choice reads it twice
     *                over, and both readings would follow the brackets
     * @param defaultGuaranteed what a position this holds no guarantee for is guaranteed to admit.
     *                Not {@link #dropped} said another way: {@code value == 5} joined with a rule
     *                nothing could read has this at {@link ValueSet#ANY} and {@code dropped} set,
     *                because the alternative that was read guarantees every value at every position
     *                it says nothing about, while a rule of the choice did go unread
     * @param guaranteedTogether whether one value may be taken from each position's guarantee and
     *                the whole of them stand together in this reading. What a conjunction needs of
     *                its sides and what a choice over more than one position does not leave
     * @param tangled the positions whose correlations this reading has lost. A union of products
     *                merged back into one product is where that happens, and a choice between
     *                alternatives written at two positions is a union no product states. Outside
     *                this set the relation factors into a product, which is what lets a position no
     *                choice reached keep its own answer
     * @param widened the positions whose {@link #at} cannot be guaranteed to be what the read rules
     *                leave them. A guarantee and not a fact: the rules below are sufficient and not
     *                necessary, so absence from this set is what is shown and presence is what is
     *                not shown either way, and a sharper reading later leaves a position out of it
     *                without anything here changing meaning.
     *
     *                <p>Held per position rather than as one answer for the reading, because the
     *                proposition is quantified over them. Read off a single flag, the only thing
     *                that can be said is that some position is not shown exact, and a reader asking
     *                about one of them is handed that sentence about each — which is the other
     *                quantifier and is false wherever a clause of its own answers for a position
     */
    public AdmissibleValues {
        standing = Collections.unmodifiableMap(new LinkedHashMap<>(standing));
        // A guarantee empty at one position is empty at all of them. What is promised is one set
        // per position standing for the product of them, and a product with an empty side is
        // empty — so there is no value at any position that this can promise. This is also where a
        // reading that admits nothing arrives, by whichever way it got there: a leaf left no value,
        // two rules that cannot both hold, a caller that showed it from outside.
        if (held instanceof Held.Nothing || defaultGuaranteed.isEmpty()
                || guaranteed.values().stream().anyMatch(ValueSet::isEmpty)) {
            guaranteed = Map.of();
            defaultGuaranteed = ValueSet.NONE;
            guaranteedTogether = true;
        }
        guaranteed = Collections.unmodifiableMap(new LinkedHashMap<>(guaranteed));
        // Kept in the order they were recorded rather than as an immutable copy, whose iteration
        // order is salted per run of the JVM: what is written out of a reading has to come out the
        // same on two compiles of one model.
        tangled = Collections.unmodifiableSet(new LinkedHashSet<>(tangled));
        widened = Collections.unmodifiableSet(new LinkedHashSet<>(widened));
    }

    /** What was said, which is what is not {@link ValueSet#ANY}: a position nothing narrowed is
     *  held by being absent, and holding it would make the same reading two states. */
    private static <A> Map<A, ValueSet> said(Map<A, ValueSet> at) {
        Map<A, ValueSet> out = new LinkedHashMap<>();
        at.forEach((atom, set) -> {
            if (!set.isAny()) {
                out.put(atom, set);
            }
        });
        return Collections.unmodifiableMap(out);
    }

    /**
     * Which values this reading can guarantee are admitted at {@code atom}, however much the rules
     * it could not read turn out to exclude.
     *
     * <p>A lower approximation where {@link #at} is an upper one, and equal to it at a position
     * this says that nothing left unread is why the answer is as wide as it is — which is what
     * {@link #speaksFor} is read from.
     *
     * <p><b>A choice composes these and a conjunction promises nothing.</b> Either alternative of a
     * choice holding is enough, so what the two of them promise a position is what either does, and
     * that is read at the position — {@code (value == 5 || value /= 5) || anything} promises every
     * value at {@code value}, whichever way its alternatives are bracketed.
     *
     * <p>A conjunction may compose them only where both sides promise their positions together.
     * What is promised is one set per position, and a choice over more than one position leaves no
     * such product: {@code (a == 5 && b == 0) || (a /= 5 && b == 1)} promises {@code a} every value
     * and {@code b} two, which as a product holds {@code a = 5, b = 1} — a pair neither alternative
     * stands for. Met with a rule admitting only {@code b = 0}, sets like that would say {@code a}
     * is still free while the rules hold it to 5. So {@link #guaranteedTogether} says whether the
     * promise is one about whole values, and a conjunction promises nothing where it is not.
     *
     * <p><b>A promise about what was read and not about what is held.</b> The alternatives above may
     * be held apart, and this is a product all the same. Which rules went unread is what it is about,
     * and holding a union does not read one of them.
     *
     * <p>Which is why {@link #speaksFor} is not answered from these under a conjunction either. A
     * rule stated beside others narrows rather than widens, so what an unread one costs there is
     * answered by the positions it names, and that is the account {@link #standing} has kept all
     * along.
     *
     * <p><b>What that costs is a promise, and it is paid across the whole value.</b> A conjunction
     * with a part nothing could read promises nothing anywhere, so a position covered inside one
     * clause is reported short of its rules once any clause of the same value goes unread —
     * {@code invariant said = (n == 5 || n /= 5) || f(n)} beside {@code invariant apart = g(m)}
     * leaves {@code n} partial, though nothing about {@code n} is what {@code g(m)} could narrow.
     * Telling the two apart wants a reading that remembers why it promises nothing, which is more
     * than a promise and less than this holds.
     */
    public ValueSet guaranteedAt(A atom) {
        return guaranteed.getOrDefault(atom, defaultGuaranteed);
    }

    /** Whether {@link #at} at {@code atom} can be guaranteed to be what the read rules leave it. */
    public boolean projectionExactAt(A atom) {
        return !widened.contains(atom);
    }

    /** Whether what this holds can be guaranteed to be the whole of what the read rules admit,
     *  which this reading guarantees where no union of alternatives was merged into one. */
    public boolean relationExact() {
        return tangled.isEmpty();
    }

    /** Nothing read and nothing missed, which is what a reading starts from. */
    public static <A> AdmissibleValues<A> top() {
        return new AdmissibleValues<>(one(new Box<>(Map.of())), Map.of(), false, Map.of(),
                ValueSet.ANY, true, Set.of(), Set.of());
    }

    /**
     * This where it already admits nothing, and a state admitting nothing where it does not.
     *
     * <p>What a caller says when something outside this showed that nothing satisfies the rules —
     * another domain reading the same clause, say. Nothing is claimed about any position: what is
     * known is about the whole, and writing it at a position would name one the rules are fine with.
     */
    public AdmissibleValues<A> leavingNothing() {
        return isBottom() ? this
                : new AdmissibleValues<>(new Held.Nothing<>(new BottomResidue<>(Map.of())),
                        standing, dropped, Map.of(), ValueSet.NONE, true, tangled, widened);
    }

    /** One position said to admit {@code set}, and nothing missed. */
    public static <A> AdmissibleValues<A> at(A atom, ValueSet set) {
        return new AdmissibleValues<>(heldBy(List.of(PairOutcome.of(Map.of(atom, set)))), Map.of(),
                false, Map.of(atom, set), ValueSet.ANY, true, Set.of(), Set.of());
    }

    /**
     * A rule this could not read, which says nothing about any position and spoils the ones it
     * names.
     *
     * <p>{@code named} may be empty — a rule reaching no position this can name is still a rule that
     * was not read, and what that costs is settled where it is joined rather than here.
     */
    public static <A> AdmissibleValues<A> unreadable(Set<A> named, UnreadReason why) {
        Map<A, UnreadReason> spoiled = new LinkedHashMap<>();
        named.forEach(each -> spoiled.put(each, why));
        // Nothing is guaranteed anywhere, and at the positions it does not name as much as at the
        // ones it does: what a rule this has no word for admits is not known, so a choice offering
        // it as an alternative is offering nothing that can be counted on.
        return new AdmissibleValues<>(one(new Box<>(Map.of())), spoiled, true, Map.of(),
                ValueSet.NONE, true, Set.of(), Set.of());
    }

    /**
     * What {@code atom} may hold, everything being admitted where nothing was said.
     *
     * <p>Over the alternatives, since a value standing in any of them stands in the reading. Which
     * is the projection of the union and is exact whatever they are written at — what a union
     * cannot state is which value at one position went with which at another, and that is not what
     * this asks.
     */
    public ValueSet at(A atom) {
        return switch (held) {
            case Held.Nothing<A> it -> it.residue().get(atom);
            case Held.Alternatives<A> it -> {
                ValueSet out = null;
                for (Box<A> box : it.boxes()) {
                    ValueSet here = box.get(atom);
                    out = out == null ? here : out.join(here);
                }
                yield out;
            }
        };
    }

    /**
     * The positions this reading narrowed, which is what a reader asking what it took in is asking.
     *
     * <p>Narrowed by the reading and not by an alternative of it: a position one alternative names
     * and another says nothing about is left at every value by the choice, and a rule that narrowed
     * nothing is not one a question can be answered from.
     */
    public Set<A> adoptedAt() {
        Set<A> out = new LinkedHashSet<>();
        adopted().forEach(atom -> {
            if (!at(atom).isAny()) {
                out.add(atom);
            }
        });
        return out;
    }

    /**
     * Whether {@link #at} is the whole of what the rules leave {@code atom}, rather than a wider
     * answer this reading could not narrow.
     *
     * <p>Either nothing was left standing at the position, or what was left standing cannot be
     * answerable for the answer's width: the two ends meet there, so every value reported is one
     * this reading can promise and there is nothing between them for an unread rule to have been.
     *
     * <p><b>Asked of the reading in hand and not settled where a rule was left standing.</b> What an
     * alternative covers is what that alternative admits, and a rule stated beside the choice may
     * leave nothing of the alternative that did the covering. In {@code (a == 5 || a /= b) && a == 7}
     * the first alternative admits every {@code b}, and the second rule refuses every value it
     * admits — so what covered {@code b} is gone, and a reading that had already struck the rule off
     * would answer that the model leaves {@code b} every value.
     */
    public boolean speaksFor(A atom) {
        return !standing.containsKey(atom) || guaranteedAt(atom).equals(at(atom));
    }

    /** What stopped this reading from speaking for {@code atom}, or null where nothing did. */
    public UnreadReason whyUnread(A atom) {
        return speaksFor(atom) ? null : standing.get(atom);
    }

    /** Whether nothing satisfies these rules, at a position or otherwise. */
    public boolean isBottom() {
        return held instanceof Held.Nothing;
    }

    /** Both readings holding at once. */
    public AdmissibleValues<A> meet(AdmissibleValues<A> other) {
        // Promising what both sides promise, where both promise their positions together. Where
        // one of them does not, the sets it holds are each true of some value and of no one value
        // at once, and met they would promise a combination neither reading has — so the
        // conjunction promises nothing. See {@link #guaranteedAt}.
        boolean apart = !guaranteedTogether || !other.guaranteedTogether;
        return new AdmissibleValues<>(met(other), union(standing, other.standing),
                dropped || other.dropped,
                // Either way what comes out is a promise about whole values, which is why a
                // conjunction never has to say it is not one. Two of them met is one — a value
                // taken from each position of both stands in both readings — and nothing promised
                // is one for want of anything to promise.
                apart ? Map.of() : guaranteedBy(guaranteed, defaultGuaranteed,
                        other.guaranteed, other.defaultGuaranteed, ValueSet::meet),
                apart ? ValueSet.NONE : defaultGuaranteed.meet(other.defaultGuaranteed),
                true,
                // The intersection of two products is a product, and of anything else it need not
                // be. What each side could not state, the conjunction cannot state either.
                both(tangled, other.tangled),
                // And a position the two of them are tangled at is where the intersection can come
                // back wider than the rules are: a pair they refuse between them is one neither
                // per-position meet excludes. Everywhere else the relation is a product and the
                // meet of a product is exact at each of its places, so those positions keep what
                // they had.
                both(both(widened, other.widened), both(tangled, other.tangled)));
    }

    /**
     * The alternatives of a conjunction: every pair of one from each side, the ones nothing stands
     * in dropped.
     *
     * <p>Distributed rather than merged first. A conjunction of a union is the union of the
     * conjunctions, and it is what leaves three of a choice's four pairs empty where the pairs are
     * held apart.
     *
     * <p>Where a side admits nothing the conjunction does, and what it is left holding is the pairs
     * it worked out all the same: a rule stated beside an impossible one is still a rule that was
     * stated, so the values it left a position are values the reading read and are answered with.
     * That is what parts a conjunction from a choice here — see {@link #join}, where nothing an
     * alternative said survives the alternative being one nobody can take.
     */
    private Held<A> met(AdmissibleValues<A> other) {
        List<PairOutcome<A>> outcomes = new ArrayList<>();
        for (Map<A, ValueSet> here : operands()) {
            for (Map<A, ValueSet> there : other.operands()) {
                Map<A, ValueSet> both = new LinkedHashMap<>(here);
                there.forEach((atom, set) -> both.merge(atom, set, ValueSet::meet));
                outcomes.add(isBottom() || other.isBottom()
                        // Shown to admit nothing, whatever the pair worked out to. A side may hold
                        // no position at all — nothing satisfies it and no position is at fault —
                        // and a pair with it is a product of what the other side said, which stands
                        // in nothing.
                        ? new PairOutcome.Dead<>(new BottomResidue<>(both))
                        : PairOutcome.of(both));
            }
        }
        return heldBy(outcomes);
    }

    /** What this holds, as the maps a conjunction is distributed over. */
    private List<Map<A, ValueSet>> operands() {
        return switch (held) {
            case Held.Nothing<A> it -> List.of(it.residue().at());
            case Held.Alternatives<A> it -> it.boxes().stream().map(Box::at).toList();
        };
    }

    /**
     * Either reading holding.
     *
     * <p>Over the positions both spoke about, since a position one of them left open is one the two
     * of them together leave open. And over the positions the other spoke about, where this branch
     * had something it could not read: those are open too, and open because of the reading rather
     * than because of the model.
     */
    public AdmissibleValues<A> join(AdmissibleValues<A> other) {
        return joining(other, false);
    }

    /**
     * Either reading holding, with the alternatives of the two held apart.
     *
     * <p>The same choice, read without merging what it leaves back into one product. A choice
     * between alternatives written at two positions is a union of two products and no product holds
     * it, so merging is where the relation goes — and it goes unnoticed, because the projections
     * survive a union and it is the next conjunction that spends what was lost.
     *
     * <p>Held apart, the conjunction meets the alternatives pairwise, the pairs nothing stands in
     * drop out, and what is left is what the rules leave. Which is why nothing is owed here: the
     * union of two products is what it is, and this states it rather than approximating it.
     *
     * <p>How many may be held is not this reading's to decide. What bounds them is settled from the
     * clauses before any of them is read ({@code ExpansionCost}), so that precision cannot turn on
     * how a fold was bracketed.
     */
    public AdmissibleValues<A> joinApart(AdmissibleValues<A> other) {
        return joining(other, true);
    }

    private AdmissibleValues<A> joining(AdmissibleValues<A> other, boolean apart) {
        // An alternative nobody can take leaves the answer to the others. Both being that is a
        // different case: no side speaks for the other, and meeting them would state a conjunction
        // the alternatives never stood in. What the choice admits nothing at is what every
        // alternative admits nothing at, and where there is no such position the choice still
        // admits nothing.
        if (isBottom() && other.isBottom()) {
            Map<A, ValueSet> both = emptyInBoth(other);
            return new AdmissibleValues<>(new Held.Nothing<>(new BottomResidue<>(both)),
                    union(standing, other.standing), dropped || other.dropped,
                    Map.of(), ValueSet.NONE, true,
                    both(tangled, other.tangled), both(widened, other.widened));
        }
        if (isBottom()) {
            return other;
        }
        if (other.isBottom()) {
            return this;
        }
        // What the alternatives guarantee between them, which is what settles whether anything is
        // left for an unread rule to have widened.
        Map<A, ValueSet> covered = guaranteedBy(guaranteed, defaultGuaranteed,
                other.guaranteed, other.defaultGuaranteed, ValueSet::join);
        ValueSet coveredElsewhere = defaultGuaranteed.join(other.defaultGuaranteed);
        Map<A, UnreadReason> spoiled = union(standing, other.standing);
        // Spoiled by there having been an alternative this could not read, which is what happened
        // to them: a value satisfying that branch is under no obligation from this one. Not by what
        // the unread rule was about — a rule relating two other positions relates this one to
        // nothing, and lending its reason here would say that it did.
        if (other.dropped) {
            spoiled = spoiling(spoiled, promisedAt());
        }
        if (dropped) {
            spoiled = spoiling(spoiled, other.promisedAt());
        }
        // What each rule left standing is kept whole. Whether a position is answerable for it is
        // read off the two ends where the question is asked ({@link #speaksFor}) rather than
        // settled here: what covers a position is an alternative, and a rule stated beside the
        // choice may leave nothing of that alternative.
        Set<A> shapedBy = new LinkedHashSet<>(promisedAt());
        shapedBy.addAll(other.promisedAt());
        // A union of two products alike everywhere but at one place is the product with that place
        // widened, so the promise survives as one about whole values where the alternatives are
        // written at no more than one position between them. Anywhere else the union holds a value
        // from one alternative at one position beside a value from the other at another, which is a
        // combination neither of them stands for.
        //
        // Sufficient and not necessary, and deliberately so. A union is also a product where one
        // alternative promises everything the other does, and where the two differ at only one
        // position however many they are written at — and both of those compare the two boxes a
        // bracketing happened to put together, so a choice of three alternatives answers one way
        // written to the left and another to the right. Measured: both were tried and both broke
        // `AChoiceIsOneConnectiveAndNotATree`. Coarse and the same either way is the trade, and
        // what it costs is a promise this could have kept rather than one it could not.
        return new AdmissibleValues<>(apart ? apart(other) : merged(other), spoiled,
                dropped || other.dropped, covered, coveredElsewhere,
                guaranteedTogether && other.guaranteedTogether && shapedBy.size() <= 1,
                // Merging a union back into one product loses a relation among the positions the
                // alternatives are written at, and outside those the two of them agree on
                // everything by saying nothing. Measured the same way the promise above is, and by
                // the same sufficient condition, so a choice at one position keeps both.
                apart || shapedBy.size() <= 1 ? both(tangled, other.tangled)
                        : both(both(tangled, other.tangled), shapedBy),
                // The projections survive whatever the alternatives are written at: the projection
                // of a union is the union of the projections.
                both(widened, other.widened));
    }

    /**
     * The one product holding both readings' alternatives, which is what a choice comes to while
     * the alternatives are held one at a time.
     *
     * <p>The keys of both and not of either: a position one side says nothing about is one the
     * choice says nothing about, since a value satisfying that side may hold anything there.
     */
    private Held<A> merged(AdmissibleValues<A> other) {
        Map<A, ValueSet> out = new LinkedHashMap<>();
        adopted().forEach(atom -> {
            ValueSet there = other.at(atom);
            if (!there.isAny()) {
                out.put(atom, at(atom).join(there));
            }
        });
        // Live by construction: a join of two sets is empty only where both are, and neither side
        // is bottom here.
        return one(new Box<>(out));
    }

    /**
     * The alternatives of both, which is what the choice leaves where they are held apart.
     *
     * <p>A set, so the same alternative offered twice is one. Neither side is bottom here, so every
     * box of either stands in the choice — nothing is dropped and nothing is merged.
     */
    private Held<A> apart(AdmissibleValues<A> other) {
        Set<Box<A>> boxes = new LinkedHashSet<>(alternatives());
        boxes.addAll(other.alternatives());
        return new Held.Alternatives<>(boxes);
    }

    /** The alternatives this holds, which a reading that admits nothing has none of. */
    private Set<Box<A>> alternatives() {
        return held instanceof Held.Alternatives<A> it ? it.boxes() : Set.of();
    }

    /** What every alternative of both admits nothing at, which is what a choice between two
     *  impossible ones leaves — and nothing else. Values an alternative nobody can take left a
     *  position are under no obligation from the choice, so they leave with it. */
    private Map<A, ValueSet> emptyInBoth(AdmissibleValues<A> other) {
        Map<A, ValueSet> out = new LinkedHashMap<>();
        adopted().forEach(atom -> {
            if (at(atom).isEmpty() && other.at(atom).isEmpty()) {
                out.put(atom, ValueSet.NONE);
            }
        });
        return out;
    }

    /** The positions this holds an answer about, in the order they were read. */
    private Set<A> adopted() {
        Set<A> out = new LinkedHashSet<>();
        switch (held) {
            case Held.Nothing<A> it -> out.addAll(it.residue().at().keySet());
            case Held.Alternatives<A> it -> it.boxes().forEach(box -> out.addAll(box.at().keySet()));
        }
        return out;
    }

    /** One alternative, which is what most readings hold. */
    private static <A> Held<A> one(Box<A> box) {
        return new Held.Alternatives<>(Set.of(box));
    }

    /**
     * What a set of worked-out pairs comes to.
     *
     * <p>Where any of them stands, those are the alternatives and the rest are combinations nothing
     * satisfies, which a union is not made wider by. Where none does, the reading admits nothing,
     * and what it is left holding is what its alternatives agree on — the projection of their union,
     * which is empty at a position exactly where every one of them is.
     */
    private static <A> Held<A> heldBy(List<PairOutcome<A>> outcomes) {
        Set<Box<A>> live = new LinkedHashSet<>();
        outcomes.forEach(each -> {
            if (each instanceof PairOutcome.Live<A> it) {
                live.add(it.box());
            }
        });
        if (!live.isEmpty()) {
            return new Held.Alternatives<>(live);
        }
        Map<A, ValueSet> residue = null;
        for (PairOutcome<A> each : outcomes) {
            Map<A, ValueSet> here = ((PairOutcome.Dead<A>) each).residue().at();
            if (residue == null) {
                residue = new LinkedHashMap<>(here);
                continue;
            }
            Map<A, ValueSet> joined = new LinkedHashMap<>();
            residue.forEach((atom, set) -> {
                ValueSet there = here.get(atom);
                if (there != null) {
                    joined.put(atom, set.join(there));
                }
            });
            residue = joined;
        }
        return new Held.Nothing<>(new BottomResidue<>(residue == null ? Map.of() : residue));
    }

    /** Every position of either, in the order they were recorded. */
    private static <A> Set<A> both(Set<A> these, Set<A> those) {
        if (those.isEmpty()) {
            return these;
        }
        if (these.isEmpty()) {
            return those;
        }
        Set<A> out = new LinkedHashSet<>(these);
        out.addAll(those);
        return out;
    }

    /** What both sides guarantee, at every position either of them holds a guarantee for, each
     *  side missing one standing at its own default. */
    private static <A> Map<A, ValueSet> guaranteedBy(Map<A, ValueSet> these, ValueSet theseElse,
                                                     Map<A, ValueSet> those, ValueSet thoseElse,
                                                     BinaryOperator<ValueSet> both) {
        Set<A> named = new LinkedHashSet<>(these.keySet());
        named.addAll(those.keySet());
        Map<A, ValueSet> out = new LinkedHashMap<>();
        named.forEach(each -> out.put(each, both.apply(these.getOrDefault(each, theseElse),
                those.getOrDefault(each, thoseElse))));
        return out;
    }

    /**
     * The positions an alternative beside this one may have widened.
     *
     * <p>Every position this reading's promise is written at, which is every position a rule of it
     * reached — narrowed there or not. Not the positions it narrows: a branch that read two rules
     * and came out admitting every value at a position narrows nothing there and had rules about it
     * all the same, and which of the two a branch looks like turns on where the brackets of the
     * choice fell. Asked of what a reading is about rather than of what it managed, the answer is
     * the same either way.
     *
     * <p>These are candidates and not the answer. What is recorded against them is that an
     * alternative went unread beside them; whether that is anything the position is answerable for
     * is settled by {@link #speaksFor}, which reads it off the two ends where the question is asked.
     * A position the alternatives cover between them carries a reason nobody is ever shown.
     */
    private Set<A> promisedAt() {
        return guaranteed.keySet();
    }

    /** The same, with {@code these} left open by an alternative — where nothing has spoiled them
     *  already. A reason already recorded for a position is a rule that named it, which is nearer
     *  than a branch that widened it from outside. */
    private static <A> Map<A, UnreadReason> spoiling(Map<A, UnreadReason> had, Set<A> these) {
        if (these.isEmpty()) {
            return had;
        }
        Map<A, UnreadReason> out = new LinkedHashMap<>(had);
        these.forEach(each -> out.putIfAbsent(each, UnreadReason.ALTERNATIVE_NOT_READ));
        return out;
    }

    private static <A> Map<A, UnreadReason> union(Map<A, UnreadReason> these,
                                                  Map<A, UnreadReason> those) {
        if (those.isEmpty()) {
            return these;
        }
        Map<A, UnreadReason> out = new LinkedHashMap<>(these);
        those.forEach(out::putIfAbsent);
        return out;
    }
}
