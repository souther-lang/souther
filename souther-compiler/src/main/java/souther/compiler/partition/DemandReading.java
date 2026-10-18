package souther.compiler.partition;

import souther.compiler.check.NumericMeasures;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.DeclaredInput;
import souther.compiler.inputs.Distinctions;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.CountsWrittenOut;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.core.ACopyOfAnApplication;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ModelOccurrences;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.BiFunction;
import java.util.function.Function;

/**
 * What one condition coming out one way asks of a row, and nothing about where it stood.
 *
 * <p>The reading of a condition and not of a way. Where a condition was met, which construct of the
 * model it is and what a report about it is sent to are the walk's, and a reader that is handed a
 * condition from somewhere that is no way at all — what a quantifier asks of each element — asks
 * this and has none of them to make up. So the answer is a {@link RowDemand} or the reason there is
 * none, and putting it on the way is {@link ReachingCuts}'s.
 *
 * <p><b>What a condition states is not read here.</b> It is the proposition the condition states
 * ({@link Pullback}), and what this does is put that proposition in the words a row is composed in:
 * a relation a region carries, a truth written at a position, a container some or every element of
 * which meets something. What those words cannot carry is said as what stopped it.
 */
final class DemandReading {

    private DemandReading() {
    }

    /**
     * How many ways an element may meet what a quantifier asks are read one by one
     * ({@link CompositionBudget#READINGS_OF_ONE_CONDITION}), read here and nowhere else.
     */
    private static final CompositionBudget READINGS = CompositionBudget.READINGS_OF_ONE_CONDITION;

    /**
     * What a condition asks of a row, or why this reading has no words for it.
     *
     * <p>Two halves, and no third. What was taken ({@link Taken}) is the condition said in a row's
     * words, whether or not anything composes a row for it; what was not ({@link Unread}) carries
     * only why the meaning was not read or the words stop. Whether a row was then found, ran, or
     * was shown impossible is the search's answer and is never written here.
     */
    sealed interface Read {

        /** What a condition asks of a row, said in a row's words. */
        sealed interface Taken extends Read {}

        /** A demand a composer can build a row against. */
        record Demands(RowDemand.OfACondition demand) implements Taken {}

        /**
         * Nothing to build against, because the answer is the same for every row: it asks nothing
         * of one where that answer is the way asked, and no row comes out of it that way where it
         * is not.
         *
         * <p>Apart from {@link Unread}, which says this reading could not state what is asked. A
         * condition the source settles was read to the end, and taken for one that was not, a way
         * past it would be reported as a way this compiler fell short on.
         */
        record Settled(boolean thisWay) implements Taken {}

        /**
         * The value at {@code at} being one of {@code cases}: a position read as some of its
         * cases, which a composer writes and the walk carries as a narrowing.
         */
        record Narrows(TermPath at, CasesLeft cases) implements Taken {

            public Narrows {
                if (at == null || cases == null) {
                    throw new IllegalArgumentException("a position is read as some of its cases");
                }
            }
        }

        /**
         * One of several things, each asked whole: a row is past the condition where it meets
         * every demand of one alternative, and an alternative is no less a way for the others
         * beside it.
         *
         * <p>A value, compared by what it holds, and hashed once: a disjunction inside an
         * alternative of another is gathered into a set at every level it nests at, and hashed
         * afresh each time, what is inside was walked once per level.
         */
        static final class OneOf implements Taken {

            /** What each alternative asks, each once and in the order the parts are kept; two or
             *  more, since one is no choice. */
            private final List<List<Read>> alternatives;
            /** The statement the alternatives are the ways of, where one proposition says it:
             *  what a composer holding all of it at once composes against without taking any one
             *  way. */
            private final Optional<Proposition> stated;
            private final int hash;

            OneOf(List<List<Read>> alternatives, Optional<Proposition> stated) {
                this.alternatives = alternatives.stream().map(List::copyOf).distinct().toList();
                if (this.alternatives.size() < 2) {
                    throw new IllegalArgumentException("one of several things is two or more: "
                            + this.alternatives);
                }
                this.stated = Objects.requireNonNull(stated, "a statement of the ways, or none");
                this.hash = 31 * this.alternatives.hashCode() + stated.hashCode();
            }

            List<List<Read>> alternatives() {
                return alternatives;
            }

            Optional<Proposition> stated() {
                return stated;
            }

            @Override
            public boolean equals(Object other) {
                return this == other || (other instanceof OneOf that && hash == that.hash
                        && alternatives.equals(that.alternatives) && stated.equals(that.stated));
            }

            @Override
            public int hashCode() {
                return hash;
            }

            @Override
            public String toString() {
                return "OneOf[alternatives=" + alternatives + "]";
            }
        }

        /** None, and everything that stopped it, each once. */
        record Unread(List<WhyNotTaken> whys) implements Read {

            Unread(WhyNotTaken why) {
                this(List.of(why));
            }

            public Unread {
                whys = List.copyOf(new LinkedHashSet<>(whys));
                if (whys.isEmpty()) {
                    throw new IllegalArgumentException("what stopped a condition is something");
                }
            }
        }
    }

    /** {@code stated}, read to the end, asked of a row as a statement only the run decides. */
    private static Read forTheRun(Proposition stated, RowDemand.NoComposer why) {
        return forTheRun(stated, why, List.of());
    }

    /** The same, with where the reading of what the values it is over were made from stopped. */
    private static Read forTheRun(Proposition stated, RowDemand.NoComposer why,
                                  List<WhyUnread> past) {
        return new Read.Demands(new RowDemand.ForTheRun(stated, why, past));
    }

    /** What a dependency answered, which a row stands in rather than writes. */
    private static Read.Unread anAnswerARowStandsIn() {
        return new Read.Unread(new WhyNotTaken.OutsideDomain(
                WhyNotTaken.DomainLimit.AN_ANSWER_A_ROW_STANDS_IN));
    }

    /**
     * One thing a condition asks, which condition of the shape asks it, and which copies of the
     * model's code each thing it asks was read off.
     *
     * @param readOff which copies {@code read}, and every read inside an alternative of it, was
     *                read off. A comparison over a value another call of a helper worked out asks
     *                what that call's fork decided beside what it compares, and the two parts are
     *                read off two calls
     */
    record Stated(Condition where, Read read, ReadOff readOff) {}

    /**
     * Which copies of the model's code each thing a condition asks was read off, by the read
     * itself.
     *
     * <p>Told where a part of the statement was read off another construct ({@link Pullback.Leaf})
     * — the fork a value the condition compares came out of, in the call that worked it out — and
     * kept by the read made of it rather than by what the read says: two parts asking one thing
     * of a row are one thing to compose against, and they may be read off two calls. A read of a
     * part nothing else was read off is what the condition itself states, in the copy it stands
     * in. And one of several things is read off what each of them was.
     */
    static final class ReadOff {

        private final Map<Read, ModelOccurrences> each;
        private final ModelOccurrences own;

        private ReadOff(Map<Read, ModelOccurrences> each, ModelOccurrences own) {
            this.each = each;
            this.own = own;
        }

        /** The copies {@code read} was read off. */
        ModelOccurrences of(Read read) {
            ModelOccurrences copies = each.get(read);
            if (copies != null) {
                return copies;
            }
            if (read instanceof Read.OneOf oneOf) {
                ModelOccurrences.Gathering out = new ModelOccurrences.Gathering();
                oneOf.alternatives().forEach(alternative -> alternative.forEach(one ->
                        out.add(of(one))));
                return out.isEmpty() ? own : out.gathered();
            }
            return own;
        }

        /**
         * What the halves of a joined condition were read off, and what the whole asks — one of
         * them, or what settles it — read off the halves it is made of.
         *
         * <p>Two halves asking alike are one alternative of what the whole asks, and the one kept
         * stands for both: what the other was read off is told of it too.
         */
        static ReadOff joined(Read made, List<List<Stated>> parts) {
            Map<Read, ModelOccurrences> each = new IdentityHashMap<>();
            ModelOccurrences.Gathering gathering = new ModelOccurrences.Gathering();
            for (List<Stated> part : parts) {
                for (Stated one : part) {
                    resolved(one.read(), one.readOff(), each);
                    gathering.add(one.readOff().own);
                }
            }
            ModelOccurrences own = gathering.gathered();
            if (made instanceof Read.OneOf oneOf) {
                ReadOff told = new ReadOff(each, own);
                for (List<Read> kept : oneOf.alternatives()) {
                    for (List<Stated> part : parts) {
                        List<Read> asked = part.stream().map(Stated::read).toList();
                        if (asked.equals(kept)) {
                            for (int at = 0; at < kept.size(); at++) {
                                joinedInto(kept.get(at), told, asked.get(at), told, each);
                            }
                        }
                    }
                }
            } else {
                ModelOccurrences.Gathering settledBy = new ModelOccurrences.Gathering();
                parts.forEach(part -> part.forEach(one -> settledBy.add(each.get(one.read()))));
                each.put(made, settledBy.gathered());
            }
            return new ReadOff(each, own);
        }

        /**
         * The same, with {@code kept} — which asks what {@code dropped} asks — told what both
         * were read off, {@code dropped} as {@code its} says, and each read inside an alternative
         * of it told so of the read at the same place in the other.
         */
        ReadOff alike(Read kept, Read dropped, ReadOff its) {
            Map<Read, ModelOccurrences> both = new IdentityHashMap<>(each);
            joinedInto(kept, this, dropped, its, both);
            return new ReadOff(both, own);
        }

        private static void joinedInto(Read kept, ReadOff mine, Read dropped, ReadOff theirs,
                                       Map<Read, ModelOccurrences> into) {
            into.put(kept, mine.of(kept).and(theirs.of(dropped)));
            if (kept instanceof Read.OneOf one && dropped instanceof Read.OneOf other) {
                for (int alternative = 0; alternative < one.alternatives().size(); alternative++) {
                    List<Read> those = one.alternatives().get(alternative);
                    List<Read> these = other.alternatives().get(alternative);
                    for (int at = 0; at < those.size(); at++) {
                        joinedInto(those.get(at), mine, these.get(at), theirs, into);
                    }
                }
            }
        }

        /** What {@code off} says {@code read} and every read inside an alternative of it were
         *  read off, into {@code into}: told by the half that read them. */
        private static void resolved(Read read, ReadOff off,
                                     Map<Read, ModelOccurrences> into) {
            into.merge(read, off.of(read), ModelOccurrences::and);
            if (read instanceof Read.OneOf oneOf) {
                oneOf.alternatives().forEach(alternative ->
                        alternative.forEach(one -> resolved(one, off, into)));
            }
        }
    }

    /**
     * One projection of a statement: what some element meeting each statement already asked, and
     * which copies of the model's code each read made of it was read off.
     *
     * <p>Told by the parts: each part of what a condition states was read off one expression, and
     * a read made of a statement is read off the parts it turns on.
     */
    private static final class Projection {

        /** What some element meeting each statement already asked, by the statement's key. */
        final Map<String, List<Read>> met = new HashMap<>();
        /** The copy each part was read off, by the part's key either way round. */
        private final Map<String, ModelOccurrences> byPart;
        /** What a read of a part read off nothing else was read off: the copy of the code that
         *  states it. */
        private final ModelOccurrences own;
        private final Map<Read, ModelOccurrences> readIn = new IdentityHashMap<>();

        private Projection(Map<String, ModelOccurrences> byPart, ModelOccurrences own) {
            this.byPart = byPart;
            this.own = own;
        }

        /** A projection nothing says the parts of. */
        static Projection unplaced() {
            return new Projection(Map.of(), ModelOccurrences.NONE);
        }

        /** A projection of what {@code pulled} states, each part read off where it was, and what
         *  nothing else was read off read off {@code own}. */
        static Projection over(Pullback.Pulled pulled, ModelOccurrences own) {
            Map<String, ModelOccurrences.Gathering> found = new LinkedHashMap<>();
            if (pulled != null) {
                for (Pullback.Leaf leaf : pulled.turnsOn()) {
                    Optional<ModelOccurrence> copy = copyOf(leaf);
                    if (copy.isPresent()) {
                        for (String key : List.of(leaf.part().key(),
                                leaf.part().denied().key())) {
                            found.computeIfAbsent(key, _ -> new ModelOccurrences.Gathering())
                                    .add(copy.get());
                        }
                    }
                }
            }
            Map<String, ModelOccurrences> byPart = new LinkedHashMap<>();
            found.forEach((key, copies) -> byPart.put(key, copies.gathered()));
            return new Projection(byPart, own);
        }

        /**
         * {@code made}, one of several things whose alternatives were {@code parts}, with what
         * every part was read off told of the alternative it is.
         *
         * <p>Two parts asking alike are one alternative, and the one kept stands for both: dropped
         * with what it was read off, a statement asking the same of two calls would name one of
         * them.
         */
        List<Read> joinedAlike(List<Read> made, List<List<Read>> parts) {
            // One of several things keeps each alternative once; anything else made of the parts
            // is the one part they all came to.
            List<List<Read>> kept = made.size() == 1 && made.getFirst() instanceof Read.OneOf oneOf
                    ? oneOf.alternatives() : List.of(made);
            for (List<Read> alternative : kept) {
                for (List<Read> part : parts) {
                    if (part.equals(alternative)) {
                        for (int at = 0; at < alternative.size(); at++) {
                            alike(alternative.get(at), part.get(at));
                        }
                    }
                }
            }
            return made;
        }

        /** {@code kept}, which asks what {@code dropped} asks, told what both were read off. */
        private void alike(Read kept, Read dropped) {
            if (kept != dropped) {
                ReadOff told = told();
                ReadOff.joinedInto(kept, told, dropped, told, readIn);
            }
        }

        /**
         * {@code reads}, made of {@code from}, each told it was read off the parts {@code from}
         * turns on where those were read off another construct.
         *
         * <p>Told of a part and of what some element meets, and not of a conjunction, of one of
         * several things or of a count of them: what those ask is what their parts ask, each read
         * off where that part was, and a read of one part told every part's copies would send a
         * reader to calls the part never read.
         */
        List<Read> readOff(List<Read> reads, Proposition from) {
            if (byPart.isEmpty() || from instanceof Proposition.All
                    || from instanceof Proposition.Any
                    || from instanceof Proposition.OnAnApplication
                    || from instanceof Proposition.SoManyHold
                    || from instanceof Proposition.SomeReachable
                    || from instanceof Proposition.WhereItAnswers) {
                return reads;
            }
            Set<String> keys = new HashSet<>();
            Pullback.Pulled.partsOf(from, keys);
            ModelOccurrences.Gathering copies = new ModelOccurrences.Gathering();
            byPart.forEach((key, those) -> {
                if (keys.contains(key)) {
                    copies.add(those);
                }
            });
            if (!copies.isEmpty()) {
                ModelOccurrences readOff = copies.gathered();
                reads.forEach(each -> readIn.putIfAbsent(each, readOff));
            }
            return reads;
        }

        /** What this projection told, with every read it told nothing of read off the copy the
         *  code that states it stands in. */
        ReadOff told() {
            return new ReadOff(readIn, own);
        }
    }

    /** The copy of the model's code {@code leaf} was read off, where it was read off one. */
    private static Optional<ModelOccurrence> copyOf(Pullback.Leaf leaf) {
        ConstructOccurrence at = ACopyOfAnApplication.occurrenceOf(leaf.from().value());
        return at != null && at.isWritten() ? ModelOccurrence.statedAt(at) : Optional.empty();
    }

    /**
     * The copy of the model's code {@code condition} stands in, which is what a part of its
     * statement read off nothing else was read off — the copies both halves stand in, for a joined
     * one.
     */
    private static ModelOccurrences own(Condition condition) {
        return switch (condition) {
            case Condition.Joined joined -> own(joined.left()).and(own(joined.right()));
            case Condition.Compares one -> ModelOccurrence.statedAt(one.stands())
                    .map(ModelOccurrences::of).orElse(ModelOccurrences.NONE);
            case Condition.Truth truth -> {
                ConstructOccurrence at = ACopyOfAnApplication.occurrenceOf(truth.value());
                yield at != null && at.isWritten()
                        ? ModelOccurrence.statedAt(at).map(ModelOccurrences::of)
                                .orElse(ModelOccurrences.NONE)
                        : ModelOccurrences.NONE;
            }
        };
    }

    /** What {@code at} states, read as the one reading of it reads it, or null for a joined
     *  condition, whose statement is its halves'. */
    private static Pullback.Pulled pulledOf(Condition at, InputReading read,
                                            WhatConditionsState conditions) {
        return switch (at) {
            case Condition.Joined _ -> null;
            case Condition.Compares one ->
                    conditions.comparison(one.comparison().stated(), one.reads(), read).stated();
            case Condition.Truth truth -> conditions.truth(truth.value(), truth.reads(), read);
        };
    }

    /**
     * What {@code stated} asks of a row, each thing put at {@code at} and read off the parts of
     * {@code at}'s statement it turns on — a proposition no condition of the shape states, such
     * as where a line of a statement of several decides.
     */
    static List<Stated> askedAt(Condition at, Proposition stated, InputReading read,
                                WhatConditionsState conditions) {
        Projected made = projectedOff(pulledOf(at, read, conditions), stated, read, own(at));
        return made.reads().stream().map(each -> new Stated(at, each, made.readOff())).toList();
    }

    /**
     * What a condition coming out {@code holding} asks of a row, one entry for each thing it asks,
     * each with the condition of the shape it was read off — the one a report about it is sent to.
     *
     * <p>A conjunction coming out the way that gives both halves asks both. The other way it says
     * one of two things, and that asks neither — {@code A && B} failing names no half that failed —
     * unless the source settles a half: one that always comes out this way settles the whole, and
     * one that never does leaves the other half as all that is said. Which nodes are conjunctions
     * is {@link Condition#of}'s answer, the one place a condition becomes a shape, and taken as it
     * gave it; and this is the one place what a conjunction asks is composed, so a way on to a
     * border and a predicate asked of each element read one connective one way.
     *
     * @param conditions what each part states, read once for every reader of the same reading
     */
    static List<Stated> stated(Condition condition, InputReading read, boolean holding,
                               WhatConditionsState conditions) {
        return switch (condition) {
            case Condition.Joined joined -> {
                List<Stated> left = stated(joined.left(), read, holding, conditions);
                List<Stated> right = stated(joined.right(), read, holding, conditions);
                if (joined.how().under(holding) == ConditionJoin.BOTH) {
                    yield List.copyOf(both(left, right));
                }
                // Each half an alternative, and each read off where that half was: the halves of
                // a condition may stand in two calls of a helper, and the one way a row takes is
                // along one of them.
                List<List<Stated>> halves = List.of(left, right);
                yield keptAlike(oneOf(halves, Stated::read,
                        (each, parts) -> new Stated(joined, each, ReadOff.joined(each, parts)),
                        Optional.of(holdingAs(statedBy(joined, read, conditions), holding))),
                        halves);
            }
            // What a comparison states, read as what it states: a size held against a number that
            // parts nought from every size above it asks what the container holding something
            // asks, and any other comparison is the relation it states.
            case Condition.Compares one -> {
                Pullback.Pulled pulled = pulledOf(one, read, conditions);
                yield statedOff(one, pulled, holding, read);
            }
            case Condition.Truth truth -> {
                Pullback.Pulled pulled = pulledOf(truth, read, conditions);
                yield statedOff(truth, pulled, holding, read);
            }
        };
    }

    /**
     * {@code made}, what one of {@code halves} came to, with what a half asking alike was read off
     * told of it too.
     *
     * <p>Where every half that could hold asks the same, the whole asks what one of them asks, and
     * that one stands for all of them: dropped with what it was read off, a condition asking the
     * same of two calls would name one of them.
     */
    private static List<Stated> keptAlike(List<Stated> made, List<List<Stated>> halves) {
        List<Read> asked = made.stream().map(Stated::read).toList();
        List<Stated> out = new ArrayList<>(made);
        for (List<Stated> half : halves) {
            if (half != made && half.stream().map(Stated::read).toList().equals(asked)) {
                for (int at = 0; at < out.size(); at++) {
                    Stated kept = out.get(at);
                    Stated other = half.get(at);
                    out.set(at, new Stated(kept.where(), kept.read(),
                            kept.readOff().alike(kept.read(), other.read(), other.readOff())));
                }
            }
        }
        return List.copyOf(out);
    }

    /** What {@code pulled}, the statement of {@code where}, coming out {@code holding} asks, each
     *  read off the parts it turns on. */
    private static List<Stated> statedOff(Condition where, Pullback.Pulled pulled,
                                          boolean holding, InputReading read) {
        Projected made = projectedOff(pulled, holdingAs(pulled.proposition(), holding), read,
                own(where));
        return made.reads().stream().map(each -> new Stated(where, each, made.readOff()))
                .toList();
    }

    /**
     * What {@code stated} asks of a row, and which copies of the model's code each read of it was
     * read off.
     *
     * @param reads   one entry for each thing it asks
     * @param readOff which copies each of them, and every read inside an alternative of one, was
     *                read off
     */
    record Projected(List<Read> reads, ReadOff readOff) {}

    /**
     * What {@code stated} — a statement {@code pulled} read, or one about what it read — asks of a
     * row, each read told the copies of the parts of {@code pulled} it is made of, and a read of a
     * part read off nothing else told {@code own}: the copy of the code that states it.
     *
     * <p>A part of a statement is read off another construct only on the way to what is compared
     * — the fork a value came out of in the call that worked it out — and is kept with that
     * construct ({@link Pullback.Leaf}). What the code itself states is no such part.
     */
    static Projected projectedOff(Pullback.Pulled pulled, Proposition stated, InputReading read,
                                  ModelOccurrences own) {
        Projection projection = Projection.over(pulled, own);
        List<Read> reads = switch (CountsWrittenOut.of(stated)) {
            case CountsWrittenOut.Written(Proposition written) ->
                    projected(written, read, projection);
            case CountsWrittenOut.PastAFigure(var figure) -> pastTheChoices(figure);
        };
        return new Projected(reads, projection.told());
    }

    /**
     * What {@code condition} coming out true states, whole, as the one reading of a truth reads it.
     *
     * @param conditions what each part states, read once for every reader of the same reading
     */
    static Proposition statedBy(Condition condition, InputReading read,
                                WhatConditionsState conditions) {
        return switch (condition) {
            case Condition.Joined joined ->
                    conditions.truth(joined.value(), joined.reads(), read).proposition();
            case Condition.Compares one -> conditions.comparison(one.comparison().stated(),
                    one.reads(), read).stated().proposition();
            case Condition.Truth truth ->
                    conditions.truth(truth.value(), truth.reads(), read).proposition();
        };
    }

    private static List<Stated> both(List<Stated> left, List<Stated> right) {
        List<Stated> out = new ArrayList<>(left);
        out.addAll(right);
        return out;
    }

    /**
     * What one of several things asks, each given as everything it asks — the one rule for a
     * disjunction, however it was written, so a condition written with {@code ||} and the same
     * condition written as a denied conjunction say the same.
     *
     * <p>Settled where one of them always comes out the way asked, and the one left where every
     * other never does — or where every other asks the same as it. Otherwise each that could be
     * what holds is one alternative ({@link Read.OneOf}); one that never comes out the way asked is
     * none.
     *
     * @param readOf  what an entry of a part is read as
     * @param asWhole an entry standing for what the whole asks, made of the parts given
     * @param stated  the statement the parts are the ways of, where one proposition says it
     */
    private static <T> List<T> oneOf(List<List<T>> parts, Function<T, Read> readOf,
                                     BiFunction<Read, List<List<T>>, T> asWhole,
                                     Optional<Proposition> stated) {
        List<List<Read>> open = new ArrayList<>();
        List<List<T>> openParts = new ArrayList<>();
        List<T> lastOpen = parts.getLast();
        for (List<T> part : parts) {
            List<Read> asked = part.stream().map(readOf).toList();
            switch (Settling.of(asked)) {
                case THIS_WAY -> {
                    return List.of(asWhole.apply(new Read.Settled(true), List.of(part)));
                }
                case NEVER -> { }
                case OPEN -> {
                    open.add(asked);
                    openParts.add(part);
                    lastOpen = part;
                }
            }
        }
        List<List<Read>> each = open.stream().distinct().toList();
        return each.size() <= 1 ? lastOpen
                : List.of(asWhole.apply(new Read.OneOf(each, stated), openParts));
    }

    /**
     * Whether what was read of a condition is settled for every row.
     *
     * <p>Never where something it asks never comes out the way asked, since all of it is asked at
     * once; the way asked where every part of it always does; and otherwise not settled.
     */
    private enum Settling {
        THIS_WAY, NEVER, OPEN;

        static Settling of(List<Read> read) {
            boolean every = true;
            for (Read each : read) {
                if (each instanceof Read.Settled(boolean thisWay)) {
                    if (!thisWay) {
                        return NEVER;
                    }
                } else {
                    every = false;
                }
            }
            return every ? THIS_WAY : OPEN;
        }
    }

    /**
     * What {@code stated} asks of a row, one entry for each thing it asks — a proposition no
     * condition of the shape states, such as where a line of a statement of several decides.
     */
    static List<Read> asked(Proposition stated, InputReading read) {
        return switch (CountsWrittenOut.of(stated)) {
            case CountsWrittenOut.Written(Proposition written) -> projected(written, read);
            case CountsWrittenOut.PastAFigure(var figure) -> pastTheChoices(figure);
        };
    }

    /**
     * What a statement holding a count of statements whose choices are not written out asks of a
     * row: nothing a row is written toward, past {@code figure}.
     *
     * <p>A count of statements is asked as the choices of which of them hold, every count in the
     * statement written out together and held to one figure ({@link CountsWrittenOut}).
     */
    private static List<Read> pastTheChoices(CompositionBudget figure) {
        return List.of(new Read.Unread(new WhyNotTaken.MoreChoicesThanAreWrittenOut(figure)));
    }

    /**
     * What an element of {@code count}'s container meeting what is counted asks: the reading a
     * condition that some element meets it comes to, read once.
     *
     * <p>Held to relations, as a region is narrowed by, where what is counted is no more than
     * relations about the element and the numbers beside it. Handed on, where it is no more than one
     * demand on another container about the element — some entry of it keyed by the element, or
     * some element of it the element's value. Neither, where it is a statement an element meets one
     * of several ways or by both at once.
     */
    static AnElementMeeting anElementMeeting(Quantity.HowManyMeet count, InputReading read) {
        List<Read> reads = asked(count.someMeets(), read);
        if (reads.size() != 1
                || !(reads.getFirst() instanceof Read.Demands(RowDemand.Exists exists))
                || !exists.ofAnElement().oneWay()) {
            return AnElementMeeting.UNREAD;
        }
        List<RowDemand.OfAnElement> way = exists.ofAnElement().theWay();
        Optional<List<TakenConstraint>> heldTo =
                exists.relations().size() == way.size()
                        ? Optional.of(exists.relations().stream()
                                .map(RowDemand.Relational::constraint).toList())
                        : Optional.empty();
        Optional<RowDemand.WithinIt> handedOn =
                way.size() == 1 && way.getFirst() instanceof RowDemand.WithinIt within
                        ? Optional.of(within) : Optional.empty();
        return new AnElementMeeting(heldTo, handedOn);
    }

    /**
     * The value at {@code at} being none of {@code cases}: one of the others its type divides into
     * ({@link Distinctions#ofType}), which no row is where there are none.
     *
     * <p>Read off the type that stands there and not off a position. A name the cases of a sum
     * share stands at one position under each case and at none of its own, and what its type
     * divides into is the same under every one of them — so the cases left are said of the name,
     * and a composer writes them under whichever case the row is.
     *
     * <p>A type stands there: the statement was read off a value at a position of the input, and
     * the reading of the input holds every position a condition names.
     */
    private static Read notOfItsCases(TermPath at, CasesLeft cases, InputReading read) {
        Type type = read.domain().typeAt(at.position(), read.rules());
        if (type == null) {
            throw new IllegalStateException("a statement of which case the value at `" + at
                    + "` is was read, and the reading of the input holds no type there");
        }
        List<Refinement> others = new ArrayList<>();
        Set<Refinement> named = Set.copyOf(cases.atoms());
        for (Case each : Distinctions.ofType(TypeView.shapeOf(type, read.rules().inners(),
                        read.rules().symbols(), read.rules().kinds(), read.rules().sums()),
                read.rules().symbols(), read.rules().kinds(), read.rules().sums())) {
            Refinement one = Refinement.of(each);
            if (one != null && !named.contains(one)) {
                others.add(one);
            }
        }
        CasesLeft left = CasesLeft.ofEach(others);
        return left == null ? new Read.Settled(false) : new Read.Narrows(at, left);
    }

    private static Proposition holdingAs(Proposition stated, boolean holding) {
        return holding ? stated : stated.denied();
    }

    /**
     * What a proposition asks of a row, one entry for each thing it asks.
     *
     * <p>Every part of a conjunction is asked; a disjunction is asked as {@link #oneOf} asks one
     * written with {@code ||}; a relation is asked where a region can carry it, and a truth where
     * it stands at a position. What some element meets, and what every element meets, are asked of the container
     * the elements are in ({@link #ofSomeElement}).
     */
    private static List<Read> projected(Proposition stated, InputReading read) {
        return projected(stated, read, Projection.unplaced());
    }

    /**
     * The same, with what some element meeting each statement already asked kept in
     * {@code projection} by the statement's key, and each read told there which copies it was
     * read off.
     *
     * <p>A count of statements about values written out is read as which of them hold, and every
     * choice names each statement, holding or failing — so one element statement is met once in
     * every choice, and the walk of the ways an element meets it is the dear part.
     *
     * <p>A read is told the parts of the statement it was made of, the parts first: what an
     * alternative or a conjunct asks was read off that part, and not off the whole the part is
     * in.
     */
    private static List<Read> projected(Proposition stated, InputReading read,
                                        Projection projection) {
        Map<String, List<Read>> met = projection.met;
        List<Read> made = switch (stated) {
            case Proposition.Always(boolean holds) -> List.of(new Read.Settled(holds));
            // A relation over anything an answer holds, a count of a list it holds among them, is
            // one a row writes no value toward. Asked once here and not of each kind of number a
            // relation weighs: a count over an answer's list is no number of the answer itself,
            // and asked by the kind it would be read as a count a row composes.
            case Proposition.Compared compared when Proposition.aboutAnAnswer(compared) ->
                    List.of(anAnswerARowStandsIn());
            case Proposition.Compared compared -> List.of(ofARelation(compared, read));
            case Proposition.Truth(DecisionSubject.AnInput(TermPath at), boolean holds, var _) ->
                    List.of(new Read.Demands(new RowDemand.ATruth(at, holds)));
            case Proposition.Truth(DecisionSubject.AnAnswer _, boolean _, var _),
                 Proposition.InCases(DecisionSubject.AnAnswer _, var _, boolean _, var _),
                 Proposition.Present(DecisionSubject.AnAnswer _, boolean _, var _) ->
                    List.of(anAnswerARowStandsIn());
            case Proposition.InCases(DecisionSubject.AnInput(TermPath at), CasesLeft cases,
                                     boolean holds, var _) ->
                    List.of(holds ? new Read.Narrows(at, cases) : notOfItsCases(at, cases, read));
            // Holding a value or holding none is which of an optional's two carriers stands there.
            case Proposition.Present(DecisionSubject.AnInput(TermPath at), boolean holds, var _) ->
                    List.of(new Read.Narrows(at,
                            CasesLeft.of(Refinement.of(new Case.Presence(holds)))));
            // A map's key being another position's value, read at one element of the map: the
            // map holds an entry filed under it.
            case Proposition.SameValue(DecisionSubject.AnInput(TermPath one),
                                       DecisionSubject.AnInput(TermPath other), boolean _, var _)
                    when keyOf(one, other) != null -> ofAnEntryKeyedAs(keyOf(one, other), stated,
                    read);
            // Two positions of the row being one value, or not, which is what a row writes at
            // them.
            case Proposition.SameValue(DecisionSubject.AnInput(TermPath one),
                                       DecisionSubject.AnInput(TermPath other), boolean holds,
                                       var _)
                    when RowDemand.OneValueAtBoth.of(one, other, holds) != null ->
                    List.of(new Read.Demands(RowDemand.OneValueAtBoth.of(one, other, holds)));
            case Proposition.SameValue _ ->
                    List.of(forTheRun(stated, RowDemand.NoComposer.TWO_SUBJECTS_ONE_VALUE));
            // The elements of a container are written alike, so the last of them is the last of
            // its value as well; that a later element holds the same value is two of them being
            // one, which no composer writes.
            case Proposition.LastToHold last -> List.of(last.holds() ? new Read.Settled(true)
                    : forTheRun(stated, RowDemand.NoComposer.TWO_SUBJECTS_ONE_VALUE));
            case Proposition.Unread unread -> List.of(new Read.Unread(
                    new WhyNotTaken.MeaningUnread(unread.why())));
            case Proposition.Carried carried -> throw carried.handedToAReader();
            case Proposition.All all -> {
                List<Read> out = new ArrayList<>();
                all.parts().forEach(part -> out.addAll(projected(part, read, projection)));
                yield List.copyOf(out);
            }
            // A row past it is one it answered at and came out this way at: both are asked.
            case Proposition.WhereItAnswers where -> {
                List<Read> out = new ArrayList<>(projected(where.answers(), read, projection));
                out.addAll(projected(where.states(), read, projection));
                yield List.copyOf(out);
            }
            case Proposition.Any any -> {
                List<List<Read>> parts = any.parts().stream()
                        .map(part -> projected(part, read, projection)).toList();
                yield projection.joinedAlike(oneOf(parts, each -> each, (each, _) -> each,
                        Optional.of(any)), parts);
            }
            case Proposition.SoManyHold _ -> throw new IllegalArgumentException(
                    "a count reaches what a row is asked written out as its choices: " + stated);
            // One of several statements, which one turning on which application a run meets the
            // condition on: one alternative per statement that can hold, as a disjunction is. A
            // statement of an application no run makes is an alternative too many and never one
            // too few, so a row is held to none of them alone — and one that holds of every row
            // settles nothing, since the application may not be one a run makes.
            case Proposition.OnAnApplication applications -> {
                List<List<Read>> open = new ArrayList<>();
                for (Proposition each : applications.each()) {
                    List<Read> asked = projected(each, read, projection);
                    if (Settling.of(asked) != Settling.NEVER) {
                        open.add(asked);
                    }
                }
                yield switch ((int) open.stream().distinct().count()) {
                    case 0 -> List.of(new Read.Settled(false));
                    case 1 -> projection.joinedAlike(open.getFirst(), open);
                    default -> projection.joinedAlike(
                            List.of(new Read.OneOf(open, Optional.of(applications))), open);
                };
            }
            // The elements of a container a dependency answered are what a row stands the
            // dependency in with and writes no value at, as the answer's own numbers are.
            case Proposition.Some some
                    when some.container() instanceof DecisionSubject.AnAnswer ->
                    List.of(anAnswerARowStandsIn());
            case Proposition.Some some -> {
                List<Read> had = met.get(some.key());
                if (had == null) {
                    had = ofSomeElement(some, read, projection);
                    met.put(some.key(), had);
                }
                yield had;
            }
            // What the search asks of the node it starts at, where that settles it, or some node
            // further down settling it, which no row is written toward.
            case Proposition.SomeReachable reached -> {
                List<List<Read>> parts = List.of(
                        projected(reached.surely(true), read, projection),
                        List.of(new Read.Unread(new WhyNotTaken.OutsideDomain(
                                WhyNotTaken.DomainLimit.A_NODE_BELOW_WHAT_A_ROW_WRITES))));
                yield projection.joinedAlike(oneOf(parts, each -> each, (each, _) -> each,
                        Optional.of(reached)), parts);
            }
        };
        return projection.readOff(made, stated);
    }

    /**
     * What some element of a container meeting something — or no element meeting it — asks of a
     * row.
     *
     * <p>No element meeting something is every element meeting its denial, so the two ways round
     * are two demands and not four. Neither is a relation a region can be narrowed by: a region
     * reads a term inside the elements as the value of one that is there, and what every element
     * meets is met by a container holding none ({@link RowDemand.ForAll}), while what some element
     * meets is met by one element and not the rest ({@link RowDemand.Exists}).
     *
     * <p>What the element is asked is said in the words an element is written in: a relation, a
     * truth or a case of a position inside it, and what a quantifier over a container inside it
     * asks of that container's elements, which are positions inside the element too. What every
     * element meets may be about what stands beside the element as well, since a container holding
     * none meets it whatever that part says, and that is the other way {@link RowDemand.ForAll}
     * is met.
     *
     * <p>Where the element may meet it several ways — one of several things it meets, or a
     * container inside it holding none where the rest of it is what every element of that
     * container meets — the ways stay inside the one demand ({@link RowDemand.AnElementMeets}).
     * Every element meeting one of several things is not every element meeting the same one of
     * them, so taken apart into one alternative per way, a row whose elements meet different ones
     * would be past the whole and along none of them. Only what a way asks of the row beside the
     * element — a part this reading could not state, or one only the run decides — parts the ways
     * into alternatives of the row, since that is no element's to meet.
     *
     * <p>The element is what stands at the container's elements — and of a map, at its keys as
     * well, since an entry is its key and its value.
     */
    private static List<Read> ofSomeElement(Proposition.Some some, InputReading read,
                                            Projection projection) {
        TermPath held = some.container().inputPosition();
        List<TermPath> element = elementOf(held);
        boolean everyElement = !some.holds();
        Proposition asked = everyElement ? some.ofTheElement().denied() : some.ofTheElement();
        List<Proposition> parts = asked instanceof Proposition.All all ? all.parts()
                : List.of(asked);
        List<List<AnElementsWay>> choices = new ArrayList<>();
        for (Proposition part : parts) {
            // What a container holding a value asks of an element is that it be that value, which
            // a composer writes into the container and no region narrows by. The element itself:
            // the key a map files it under being a value is no value the map holds.
            List<AnElementsWay> these = part instanceof Proposition.SameValue(
                    DecisionSubject.AnInput(TermPath one), DecisionSubject.AnInput(TermPath at),
                    boolean holds, var _) && one.equals(held.element())
                    ? List.of(AnElementsWay.asking(holds ? new RowDemand.SameAs(at)
                            : new RowDemand.DifferentFrom(at)))
                    : keyedWays(part, held, element);
            choices.add(these != null ? these
                    : waysOf(projected(part, read, projection), element, everyElement, some,
                    read));
        }
        List<AnElementsWay> ways = AnElementsWay.eachWhole(choices, read);
        Optional<Quantity.HowManyMeet> counted = countOf(some);
        return everyElement ? everyElementMeeting(held, ways, read, counted, Optional.of(some))
                : someElementMeeting(held, ways, read, counted, Optional.of(some));
    }

    /**
     * How many elements meet what {@code some} states of one, where that is a count a row can be
     * composed for: a statement read through, about the element.
     */
    private static Optional<Quantity.HowManyMeet> countOf(Proposition.Some some) {
        Proposition statement = some.ofTheElement();
        return statement.mayTurnOnAnElementOf(some.container())
                && !Proposition.leavesSomethingUnread(statement)
                && AStatementAtARow.askable(statement)
                ? Optional.of(new Quantity.HowManyMeet(some.container(), statement))
                : Optional.empty();
    }

    /**
     * How many times the ways an element may meet a statement have been walked, for a test holding
     * the readers of one input to walking the same parts once.
     *
     * <p>Counted rather than timed, for the reason {@link
     * souther.compiler.check.InvariantChecker#readingsMade} gives: what is held is that asking the
     * same parts again walks nothing, which is a shape and not a speed.
     */
    static long walksMade() {
        return AnElementsWay.WALKS.get();
    }

    /**
     * One way an element may meet what is asked of it: what it is asked, what is asked of the row
     * beside it, and whether no element meets it at all.
     *
     * @param ofTheElement what the element is asked
     * @param ofTheRow     what is asked of the row whichever element it is — a part about nothing
     *                     of the element, one this reading could not state, or one only the run
     *                     decides
     * @param never        whether something asked of the element is something no element meets
     */
    private record AnElementsWay(List<RowDemand.OfAnElement> ofTheElement, List<Read> ofTheRow,
                                 boolean never) {

        static final AnElementsWay ASKING_NOTHING = new AnElementsWay(List.of(), List.of(), false);

        static final AnElementsWay NEVER = new AnElementsWay(List.of(), List.of(), true);

        AnElementsWay {
            ofTheElement = List.copyOf(ofTheElement);
            ofTheRow = List.copyOf(ofTheRow);
        }

        static AnElementsWay asking(RowDemand.OfAnElement one) {
            return new AnElementsWay(List.of(one), List.of(), false);
        }

        static AnElementsWay asking(List<RowDemand.OfAnElement> these) {
            return new AnElementsWay(these, List.of(), false);
        }

        static AnElementsWay ofTheRow(Read one) {
            return new AnElementsWay(List.of(), List.of(one), false);
        }

        /**
         * The ways a figure of this compiler's work left unlooked at, as one way of their own: the
         * row is asked something nothing here read, which is neither a way no element meets nor
         * one an element is composed for. Kept beside the ways that were looked at, so those are
         * composed for and a way past all of them is not said to be closed.
         */
        static final AnElementsWay LEFT_UNREAD = ofTheRow(
                new Read.Unread(new WhyNotTaken.MoreWaysThanAreRead()));

        /**
         * Every way of taking one choice of each of {@code parts} together, each whole.
         *
         * <p>Any of them meeting is enough, whether some element is asked it or every element is:
         * a row along one way meets what all of them ask together. So the ways are made whole one
         * at a time and those made are kept however many are not, with {@link #LEFT_UNREAD} beside
         * them where a figure stopped the making — what is kept is composed for, and what was not
         * looked at is said to be so rather than lost or taken as closed.
         *
         * <p>A way no element meets is not taken further: some element meeting it is no row's, and
         * every element meeting it is the container holding none, whatever else is asked beside
         * it. Which ways those are is proved and not guessed: what the declarations leave, which is
         * what every element holds, with the relations the way asks of the element taken in, left
         * with nothing ({@link TakenConstraint#nothingMeetsAll}). A choice between relations of one
         * number written as a conjunction of disjunctions is, taken apart, mostly ways like that.
         *
         * <p>What is looked at is held to the figure — each way a choice of several opens — whether
         * or not it turns out closed, so a walk among closed ways stops where it is told to.
         */
        static List<AnElementsWay> eachWhole(List<List<AnElementsWay>> parts, InputReading read) {
            return read.derived(Walked.class, _ -> new Walked())
                    .filed.computeIfAbsent(parts, asked -> walkedWhole(asked, read));
        }

        private static final AtomicLong WALKS = new AtomicLong();

        /**
         * The ways made whole out of each list of parts, kept with the reading they were walked in.
         *
         * <p>What a walk makes is settled by the parts and by what the declarations leave every
         * element, which is this reading's, so the same parts walked again come to the same ways.
         * And the same parts are walked again many times: a choice between statements is read
         * wherever a statement it names is asked, and each of those readings walks it. Kept by the
         * reading rather than by one question asked of it, because the questions that ask the same
         * parts are many and each one is asked from its own start.
         */
        private static final class Walked {

            private final Map<List<List<AnElementsWay>>, List<AnElementsWay>> filed =
                    new ConcurrentHashMap<>();
        }

        /** {@link #eachWhole}, worked out. */
        private static List<AnElementsWay> walkedWhole(List<List<AnElementsWay>> parts,
                                                       InputReading read) {
            WALKS.incrementAndGet();
            Set<AnElementsWay> open = new LinkedHashSet<>();
            int[] looked = {0};
            if (!walk(parts, 0, ASKING_NOTHING, read.quantities().region(), open, looked)) {
                open.add(LEFT_UNREAD);
            }
            return open.isEmpty() ? List.of(NEVER) : List.copyOf(open);
        }

        /**
         * {@code so} taken one choice of each part from {@code at} on, each way made whole put in
         * {@code open}.
         *
         * @param within what the declarations leave with every relation {@code so} asks of the
         *               element taken in, carried down the walk so each choice narrows it by what
         *               it adds and no more
         * @return whether every way was looked at, which is false where the figure stopped it
         */
        private static boolean walk(List<List<AnElementsWay>> parts, int at, AnElementsWay so,
                                    SearchRegion within, Set<AnElementsWay> open, int[] looked) {
            if (at == parts.size()) {
                open.add(so);
                return true;
            }
            int most = READINGS.maximum();
            List<AnElementsWay> choices = parts.get(at);
            // A part with one choice is taken and not chosen, so a long conjunction of single
            // relations costs nothing of the figure: what is counted is each way a choice opens.
            boolean aChoice = choices.size() > 1;
            for (AnElementsWay choice : choices) {
                if (aChoice) {
                    if (looked[0] == most) {
                        return false;
                    }
                    looked[0]++;
                }
                if (choice.never) {
                    continue;
                }
                List<TakenConstraint> added = relationsOf(choice);
                SearchRegion further = added.isEmpty() ? within
                        : TakenConstraint.narrowedBy(added, within);
                if (!added.isEmpty() && TakenConstraint.nothingIsLeftFor(added, further)) {
                    continue;
                }
                if (!walk(parts, at + 1, so.with(choice), further, open, looked)) {
                    return false;
                }
            }
            return true;
        }

        /** The relations {@code way} asks of the element, which are what a region is narrowed
         *  by. */
        private static List<TakenConstraint> relationsOf(AnElementsWay way) {
            List<TakenConstraint> out = new ArrayList<>();
            for (RowDemand.OfAnElement each : way.ofTheElement) {
                if (each instanceof RowDemand.Relational(TakenConstraint relation)) {
                    out.add(relation);
                }
            }
            return out;
        }

        /**
         * The ways of every one of {@code alternatives}, any of which is enough.
         *
         * <p>One no element meets is none of them, and only where every one is closed is the
         * whole. Those left open are held to the figure, and past it the rest are said to be
         * {@link #LEFT_UNREAD} and not dropped: the ones kept are composed for all the same.
         */
        static List<AnElementsWay> oneOfEach(List<List<AnElementsWay>> alternatives) {
            int most = READINGS.maximum();
            Set<AnElementsWay> open = new LinkedHashSet<>();
            boolean someLeft = false;
            for (List<AnElementsWay> alternative : alternatives) {
                for (AnElementsWay way : alternative) {
                    if (way.never || open.contains(way)) {
                        continue;
                    }
                    if (open.size() == most) {
                        someLeft = true;
                        break;
                    }
                    open.add(way);
                }
            }
            if (someLeft) {
                open.add(LEFT_UNREAD);
            }
            return open.isEmpty() ? List.of(NEVER) : List.copyOf(open);
        }

        /** This way and {@code choice} together; whether an element meets them is the walk's to
         *  ask ({@link #walk}). */
        private AnElementsWay with(AnElementsWay choice) {
            List<RowDemand.OfAnElement> element = new ArrayList<>(ofTheElement);
            element.addAll(choice.ofTheElement);
            List<Read> row = new ArrayList<>(ofTheRow);
            row.addAll(choice.ofTheRow);
            return new AnElementsWay(element, row, false);
        }
    }

    /**
     * The ways an element may meet what {@code reads} asks of it, each part of it taken together
     * with every other.
     *
     * @param whole what the quantifier states, which is what a part only the run decides asks of
     *              the run
     */
    private static List<AnElementsWay> waysOf(List<Read> reads, List<TermPath> element,
                                              boolean everyElement, Proposition.Some whole,
                                              InputReading read) {
        List<List<AnElementsWay>> choices = new ArrayList<>();
        for (Read each : reads) {
            choices.add(choicesOf(each, element, everyElement, whole, read));
        }
        return AnElementsWay.eachWhole(choices, read);
    }

    /**
     * The ways an element may meet what one entry asks.
     *
     * <p>What some element meets, the parts of it about nothing of the element hold of the row
     * whichever element it is, so those are what the row is asked like any other. What every
     * element meets is asked of the element whatever it is about, since a container holding none
     * meets all of it.
     */
    private static List<AnElementsWay> choicesOf(Read each, List<TermPath> element,
                                                 boolean everyElement, Proposition.Some whole,
                                                 InputReading read) {
        return switch (each) {
            case Read.Unread _ -> List.of(AnElementsWay.ofTheRow(each));
            // Met by every element whatever it is, which holds the element to nothing.
            case Read.Settled(boolean thisWay) ->
                    List.of(thisWay ? AnElementsWay.ASKING_NOTHING : AnElementsWay.NEVER);
            case Read.Demands(RowDemand.Relational relation) ->
                    List.of(everyElement || aboutAny(relation, element)
                            ? AnElementsWay.asking(relation) : AnElementsWay.ofTheRow(each));
            case Read.Demands(RowDemand.ATruth truth) ->
                    List.of(everyElement || inside(truth.at(), element)
                            ? AnElementsWay.asking(truth) : AnElementsWay.ofTheRow(each));
            case Read.Narrows(TermPath at, var cases) -> everyElement || inside(at, element)
                    ? aCaseOfTheElement(at, cases, read)
                    : List.of(AnElementsWay.ofTheRow(each));
            // A quantifier over a container: what it asks of its own elements is asked of
            // positions inside the element, where the container is inside it.
            // Some element of it meeting one of several things is a way of the outer element for
            // each of them, exactly.
            case Read.Demands(RowDemand.Exists inner) -> {
                if (!everyElement && !anyInside(inner.positions(), element)) {
                    yield List.of(AnElementsWay.ofTheRow(each));
                }
                List<AnElementsWay> out = new ArrayList<>();
                for (List<RowDemand.OfAnElement> way : inner.ofAnElement().ways()) {
                    out.add(AnElementsWay.asking(within(inner.container(), true, way)));
                }
                yield out;
            }
            // And every element of such a container meeting something is elements that meet it,
            // or the container holding none. A container inside an element is written alike in
            // every element, so each of its elements meeting one way is a way of the outer
            // element, and elements of it meeting different ones are not written.
            case Read.Demands(RowDemand.ForAll inner) -> {
                if (!everyElement && !anyInside(inner.positions(), element)) {
                    yield List.of(AnElementsWay.ofTheRow(each));
                }
                List<AnElementsWay> out = new ArrayList<>();
                for (List<RowDemand.OfAnElement> way : inner.ofEachElement().ways()) {
                    out.add(AnElementsWay.asking(within(inner.container(), false, way)));
                }
                out.add(AnElementsWay.asking(inner.holdingNone()));
                yield out;
            }
            case Read.Demands(RowDemand.SoMany count) ->
                    List.of(everyElement || anyInside(count.positions(), element)
                            ? AnElementsWay.ofTheRow(forTheRun(whole,
                                    RowDemand.NoComposer.A_COUNT_WITHIN_AN_ELEMENT))
                            : AnElementsWay.ofTheRow(each));
            // Two values being one, asked of the row where neither is inside the element. Inside
            // it, the element is written alike with every other and no value is written into it
            // from another position here.
            case Read.Demands(RowDemand.OneValueAtBoth both) ->
                    List.of(everyElement || anyInside(both.positions(), element)
                            ? AnElementsWay.ofTheRow(forTheRun(whole,
                                    RowDemand.NoComposer.TWO_SUBJECTS_ONE_VALUE))
                            : AnElementsWay.ofTheRow(each));
            case Read.Demands(RowDemand.ForTheRun(var _, var why, var past)) ->
                    List.of(AnElementsWay.ofTheRow(forTheRun(whole, why, past)));
            // Each way of each alternative: one alternative a figure stopped is said to be, and
            // the others are the ways they are.
            case Read.OneOf oneOf -> {
                List<List<AnElementsWay>> ofEach = new ArrayList<>();
                for (List<Read> alternative : oneOf.alternatives()) {
                    ofEach.add(waysOf(alternative, element, everyElement, whole, read));
                }
                yield AnElementsWay.oneOfEach(ofEach);
            }
        };
    }

    /**
     * The element's value at {@code at} being one of {@code cases}, as what the declarations leave
     * every element says: asked of the element where they leave it more than those — with the
     * places on its order the cases left out, as a narrowing on the way carries them — met by
     * every element where they leave it only those, and by none where they leave it none of them.
     */
    private static List<AnElementsWay> aCaseOfTheElement(TermPath at, CasesLeft cases,
                                                         InputReading read) {
        return List.of(switch (ReachingCuts.taking(at, cases, read)) {
            case DeclaredInput.Taking.Narrows(TermPath to) -> {
                List<RowDemand.OfAnElement> asked = new ArrayList<>();
                asked.add(new RowDemand.InCases(to, read.domain().reach().crossings()));
                for (TakenConstraint.AwayFrom hole : ReachingCuts.onItsOrder(to, read)) {
                    asked.add(new RowDemand.Relational(hole));
                }
                yield AnElementsWay.asking(asked);
            }
            case DeclaredInput.Taking.Implied _ -> AnElementsWay.ASKING_NOTHING;
            case DeclaredInput.Taking.Excluded _ -> AnElementsWay.NEVER;
        });
    }

    /**
     * What an entry of the map at {@code map} being filed under a key — or under another than it —
     * asks of a row: the map holds one, which is some element of it asked this.
     */
    private static List<Read> ofAnEntryKeyedAs(TermPath map, Proposition stated,
                                                InputReading read) {
        List<AnElementsWay> ways = keyedWays(stated, map, elementOf(map));
        if (ways == null) {
            return List.of(forTheRun(stated, RowDemand.NoComposer.TWO_SUBJECTS_ONE_VALUE));
        }
        return someElementMeeting(map, ways, read, Optional.empty(), Optional.of(stated));
    }

    /**
     * The map one of {@code one} and {@code other} is the keys of, where the other is no position
     * of it — or null where neither is a map's keys, or both stand at the same map.
     */
    private static TermPath keyOf(TermPath one, TermPath other) {
        TermPath map = one.mapOfTheKeys() != null ? one.mapOfTheKeys() : other.mapOfTheKeys();
        TermPath at = one.mapOfTheKeys() != null ? other : one;
        return map == null || at.isAtOrUnder(map) ? null : map;
    }

    /**
     * What an element of the map at {@code held} is asked where {@code part} says its key is, or is
     * not, the value at another position — or null where {@code part} says no such thing.
     */
    private static List<AnElementsWay> keyedWays(Proposition part, TermPath held,
                                                 List<TermPath> element) {
        if (!(part instanceof Proposition.SameValue(DecisionSubject.AnInput(TermPath one),
                DecisionSubject.AnInput(TermPath other), boolean holds, var _))) {
            return null;
        }
        TermPath key = held.key();
        TermPath at = one.equals(key) ? other : other.equals(key) ? one : null;
        if (at == null || inside(at, element)) {
            return null;
        }
        return List.of(AnElementsWay.asking(holds ? new RowDemand.KeyedAs(at)
                : new RowDemand.NotKeyedAs(at)));
    }

    /**
     * What a quantifier over the container at {@code container} asks of its elements, as what is
     * asked of positions inside the element of the outer one: what names its own position as it
     * is, and an element being another position's value as that of the inner container.
     */
    private static List<RowDemand.OfAnElement> within(TermPath container, boolean some,
                                                      List<RowDemand.OfAnElement> asked) {
        List<RowDemand.OfAnElement> out = new ArrayList<>();
        for (RowDemand.OfAnElement each : asked) {
            out.add(switch (each) {
                case RowDemand.SameAs _, RowDemand.DifferentFrom _, RowDemand.KeyedAs _,
                     RowDemand.NotKeyedAs _ -> new RowDemand.WithinIt(container, some, each);
                case RowDemand.Relational _, RowDemand.ATruth _, RowDemand.InCases _,
                     RowDemand.WithinIt _ -> each;
            });
        }
        return List.copyOf(out);
    }

    /**
     * What some element meeting one of {@code ways} asks of a row.
     *
     * <p>Some element meeting one of several things is some element meeting the first or some
     * meeting the second, so the ways that ask the row the same beside the element are one demand
     * with those ways inside it, and ways asking the row different things are alternatives of the
     * row. One no element meets is none of them, and where every one is that, no row is past it.
     *
     * @param counted how many elements meet the statement, which the demand is where it is the
     *                whole of it: one demand, asking nothing of the row beside the element
     * @param stated  the statement read, where one proposition says it
     */
    private static List<Read> someElementMeeting(TermPath held, List<AnElementsWay> ways,
                                                 InputReading read,
                                                 Optional<Quantity.HowManyMeet> counted,
                                                 Optional<Proposition> stated) {
        RowDemand.Relational holdingOne = sizeAgainst(held, read, true);
        Map<List<Read>, List<List<RowDemand.OfAnElement>>> byTheRow = new LinkedHashMap<>();
        Set<List<Read>> anyElement = new LinkedHashSet<>();
        for (AnElementsWay way : ways) {
            if (way.never()) {
                continue;
            }
            List<List<RowDemand.OfAnElement>> these =
                    byTheRow.computeIfAbsent(way.ofTheRow(), _ -> new ArrayList<>());
            // An element meeting nothing this reading could state is any element, and the
            // container holding one is all that is left to ask.
            if (way.ofTheElement().isEmpty()) {
                anyElement.add(way.ofTheRow());
            } else {
                these.add(way.ofTheElement());
            }
        }
        if (byTheRow.isEmpty()) {
            return List.of(new Read.Settled(false));
        }
        boolean whole = byTheRow.size() == 1 && byTheRow.containsKey(List.of());
        List<List<Read>> alternatives = new ArrayList<>();
        byTheRow.forEach((ofTheRow, ofTheElement) -> {
            List<Read> out = new ArrayList<>(ofTheRow);
            out.add(new Read.Demands(anyElement.contains(ofTheRow) ? holdingOne
                    : new RowDemand.Exists(held, new RowDemand.AnElementMeets(ofTheElement),
                            holdingOne, whole ? counted : Optional.empty())));
            alternatives.add(List.copyOf(out));
        });
        return oneOf(alternatives, each -> each, (each, _) -> each, stated);
    }

    /**
     * What every element meeting one of {@code ways} asks of a row.
     *
     * <p>One demand, each element along whichever of the ways it meets — the ways that ask
     * nothing of the row beside the element. A way that does ask the row something is no
     * element's to meet: the row meeting it and every element meeting that way or one of the
     * others is enough, so it is an alternative of the row, beside every element meeting one of
     * the rest. A way no element meets is none of them, and where every one is that, the container
     * holds none and nothing else is asked of an element that is not there.
     *
     * @param counted how many elements meet the statement whose denial every element is to meet,
     *                which the demand is where it is the whole of it
     * @param stated  the statement read, where one proposition says it
     */
    private static List<Read> everyElementMeeting(TermPath held, List<AnElementsWay> ways,
                                                  InputReading read,
                                                  Optional<Quantity.HowManyMeet> counted,
                                                  Optional<Proposition> stated) {
        RowDemand.Relational holdingNone = sizeAgainst(held, read, false);
        List<List<RowDemand.OfAnElement>> ofTheElement = new ArrayList<>();
        List<AnElementsWay> withTheRow = new ArrayList<>();
        for (AnElementsWay way : ways) {
            if (way.never()) {
                continue;
            }
            if (!way.ofTheRow().isEmpty()) {
                withTheRow.add(way);
            } else if (way.ofTheElement().isEmpty()) {
                // Every element meeting what every element meets, whatever the container holds.
                return List.of(new Read.Settled(true));
            } else {
                ofTheElement.add(way.ofTheElement());
            }
        }
        if (ofTheElement.isEmpty() && withTheRow.isEmpty()) {
            return List.of(new Read.Demands(holdingNone));
        }
        List<List<Read>> alternatives = new ArrayList<>();
        if (!ofTheElement.isEmpty()) {
            alternatives.add(List.of(new Read.Demands(new RowDemand.ForAll(held,
                    new RowDemand.AnElementMeets(ofTheElement), holdingNone,
                    withTheRow.isEmpty() ? counted : Optional.empty()))));
        }
        for (AnElementsWay way : withTheRow) {
            List<Read> out = new ArrayList<>(way.ofTheRow());
            if (!way.ofTheElement().isEmpty()) {
                List<List<RowDemand.OfAnElement>> these = new ArrayList<>(ofTheElement);
                these.add(way.ofTheElement());
                out.add(new Read.Demands(new RowDemand.ForAll(held,
                        new RowDemand.AnElementMeets(these), holdingNone, Optional.empty())));
            }
            alternatives.add(List.copyOf(out));
        }
        return alternatives.size() == 1 ? alternatives.getFirst()
                : oneOf(alternatives, each -> each, (each, _) -> each, stated);
    }

    /**
     * Where an element of the container at {@code held} stands: at its elements, and at its keys —
     * which only a map has, so of anything else nothing stands there.
     */
    private static List<TermPath> elementOf(TermPath held) {
        return List.of(held.element(), held.key());
    }

    /** Whether {@code at} stands inside the element. */
    private static boolean inside(TermPath at, List<TermPath> element) {
        return element.stream().anyMatch(at::isAtOrUnder);
    }

    /** Whether some of {@code positions} stands inside the element. */
    private static boolean anyInside(Set<TermPath> positions, List<TermPath> element) {
        return positions.stream().anyMatch(each -> inside(each, element));
    }

    /** Whether some term {@code relation} is over stands inside the element. */
    private static boolean aboutAny(RowDemand.Relational relation, List<TermPath> element) {
        return relation.constraint().terms().stream().anyMatch(term ->
                element.stream().anyMatch(term.subjectPath()::isAtOrUnder));
    }

    /**
     * That the container at {@code held} holds at least one, or none, as its size against one or
     * against nought.
     *
     * <p>The size is the one that counts what a value of the container's type holds
     * ({@link NumericMeasures#takenOf}), and there always is one. A statement about some element
     * of a container is read off a container standing at a position of the input, every type a
     * container can be measures how many it holds, and the reading of the input holds every
     * position a condition names — so a container whose size this cannot say is the reading
     * contradicting what it read, and is said as that.
     */
    private static RowDemand.Relational sizeAgainst(TermPath held, InputReading read,
                                                    boolean atLeastOne) {
        Type container = read.domain().typeAt(held, read.rules());
        ValueName.Stdlib size = container == null ? null
                : NumericMeasures.takenOf(container, read.rules().inners());
        NumericTerm.TakenOf count = size == null ? null : NumericTerm.TakenOf.asItStands(size, held,
                container, read.rules().inners(), read.rules().symbols());
        if (count == null) {
            throw new IllegalStateException("a statement about the elements of `" + held
                    + "` was read, and the reading of the input measures no size of it: "
                    + container);
        }
        // `count - 1 >= 0`, or `count <= 0`.
        LinearForm<NumericTerm> form = atLeastOne
                ? LinearForm.<NumericTerm>atomMinusConstant(count, ExactRatio.ONE)
                : LinearForm.<NumericTerm>atom(count);
        Rel rel = atLeastOne ? Rel.GE : Rel.LE;
        return switch (read.quantities().region().assuming(form, rel)) {
            case SearchRegion.Assumption.Taken _ ->
                    new RowDemand.Relational(new TakenConstraint.Affine(form, rel));
            case SearchRegion.Assumption.Refused(var why) -> throw new IllegalStateException(
                    "how many `" + held + "` holds is a count, and a region refused it: " + why);
        };
    }

    /**
     * What a relation coming out the way it does asks of a row, where a region can carry it.
     *
     * <p>Whether a region can carry it is asked of a region rather than decided from the shape of
     * the form. That a reading reached the end of a comparison is a fact about the arithmetic's
     * reading; whether the values it is over stand on anything a region measures them on is the
     * region's, and the two are not each other — a difference between two positions holding records
     * is read perfectly and is a distance on nothing.
     *
     * <p>A relation on an order is a bound where the relation says where the run stops and a hole
     * where it does not, which are two shapes and not one with a flag: an end moves where a chooser
     * looks, and a hole leaves the run where it was and takes one value out of it.
     */
    private static Read ofARelation(Proposition.Compared compared, InputReading read) {
        Rel proposition = compared.relation().proposition();
        Rel met = compared.holds() ? proposition : proposition.denied();
        return switch (compared.relation()) {
            // How many elements meet a statement against a number, which is no number a row
            // writes and is composed for: the count is held against the one number the form
            // weighs it against, and its weight is above nought, as a relation's first weight is.
            case Relation.Affine affine
                    when AStatementAtARow.countIn(affine) instanceof Quantity.HowManyMeet count
                    && AStatementAtARow.askable(count.ofTheElement()) -> {
                ExactRatio weight = affine.form().coefs().values().iterator().next();
                yield affine.form().constant().negated().dividedBy(weight)
                        instanceof ExactAnswer.Held<ExactRatio>(ExactRatio level)
                        ? new Read.Demands(new RowDemand.SoMany(count, met, level,
                                new LinearForm<>(ExactRatio.ZERO, Map.of()),
                                anElementMeeting(count, read)))
                        : forTheRun(compared, RowDemand.NoComposer.A_COUNT_AGAINST_A_NUMBER_NOT_HELD);
            }
            // The same count with numbers of the input added to it. Scaled to weigh the count by
            // one, so what a row is asked for is the count and the form it is to come to together
            // and not a count against a number that is not yet there.
            case Relation.Affine affine when countAndNumbers(affine, read) != null ->
                    soManyAgainstNumbers(compared, affine, met, read);
            case Relation.Affine(LinearForm<Quantity> form, Rel _) -> {
                LinearForm<NumericTerm> against = WhatTheDeclarationsLeave.ofTheInput(form);
                if (against == null) {
                    yield overNoRowNumber(compared, form);
                }
                yield switch (read.quantities().region().assuming(against, met)) {
                    case SearchRegion.Assumption.Taken _ -> new Read.Demands(
                            new RowDemand.Relational(new TakenConstraint.Affine(against, met)));
                    // Two values on no order held equal or unequal, which is what a row writes
                    // and not a relation a region places. Held one above the other, they are a
                    // distance on nothing, and the region's word for why is what is said.
                    case SearchRegion.Assumption.Refused(var why) -> {
                        RowDemand.OneValueAtBoth both = oneValueAtBoth(against, met);
                        yield both != null ? new Read.Demands(both)
                                : new Read.Unread(whyDeclined(why));
                    }
                };
            }
            case Relation.Ordered(DecisionAtom.OfTheInput(NumericTerm.FromOnePosition term),
                                  var at, Rel _) ->
                    new Read.Demands(new RowDemand.Relational(TakenConstraint.Ordered.isABound(met)
                            ? new TakenConstraint.Ordered(term, at, met)
                            : new TakenConstraint.AwayFrom(term, at)));
            case Relation.Ordered _ ->
                    forTheRun(compared, RowDemand.NoComposer.AN_ORDER_OF_NO_ONE_POSITION);
        };
    }

    /**
     * The count {@code affine} weighs beside numbers of the input, or null where it is no such
     * relation: one count a row is composed for, and nothing but numbers a row writes at one place
     * each beside it.
     */
    private static Quantity.HowManyMeet countAndNumbers(Relation.Affine affine,
                                                        InputReading read) {
        if (affine.form().coefs().size() < 2) {
            return null;
        }
        Quantity.HowManyMeet count = null;
        for (Quantity each : affine.form().coefs().keySet()) {
            if (each instanceof Quantity.HowManyMeet counted && count == null) {
                count = counted;
            } else if (each instanceof DecisionAtom.OfTheInput(NumericTerm term)
                    && term.atOnePosition() != null) {
                TermOrders orders = read.quantities().ordersOf(term);
                if (orders == null || orders.observed() == null || orders.answered() == null
                        || !orders.answered().counts()) {
                    return null;
                }
            } else {
                return null;
            }
        }
        return count != null && AStatementAtARow.askable(count.ofTheElement()) ? count : null;
    }

    /**
     * That so many elements of a container meet a statement, with numbers of the input added to
     * the count, as what a row is asked: the relation scaled to weigh the count by one, turned over
     * where that takes a negative.
     */
    private static Read soManyAgainstNumbers(Proposition.Compared compared,
                                             Relation.Affine affine, Rel met, InputReading read) {
        Quantity.HowManyMeet count = countAndNumbers(affine, read);
        ExactRatio weight = affine.form().coefs().get(count);
        if (!(ExactRatio.ONE.dividedBy(weight) instanceof ExactAnswer.Held<ExactRatio>(
                ExactRatio scale))
                || !(affine.form().times(scale) instanceof ExactAnswer.Held<LinearForm<Quantity>>(
                        LinearForm<Quantity> scaled))) {
            return forTheRun(compared, RowDemand.NoComposer.A_COUNT_AGAINST_A_NUMBER_NOT_HELD);
        }
        Map<NumericTerm, ExactRatio> added = new LinkedHashMap<>();
        scaled.coefs().forEach((quantity, by) -> {
            if (quantity instanceof DecisionAtom.OfTheInput(NumericTerm term)) {
                added.put(term, by);
            }
        });
        return new Read.Demands(new RowDemand.SoMany(count,
                scale.signum() < 0 ? met.turned() : met, scaled.constant().negated(),
                new LinearForm<>(ExactRatio.ZERO, added), anElementMeeting(count, read)));
    }

    /**
     * What a relation over {@code form}, which is over some number no row writes, asks of a row.
     *
     * <p>What a dependency answered is no number a row writes, and is said as that. Otherwise the
     * relation is asked of the run: a value the body works out, or how many elements meet
     * something, is a number a row comes to and not one it writes, and only the count has a
     * composer at all — for a count alone against a number, which this is not.
     */
    private static Read overNoRowNumber(Proposition.Compared compared, LinearForm<Quantity> form) {
        boolean counted = false;
        boolean overElements = false;
        boolean remainder = false;
        boolean remainderByAnInput = false;
        boolean product = false;
        boolean answered = false;
        List<WhyUnread> past = new ArrayList<>();
        for (Quantity atom : form.coefs().keySet()) {
            switch (atom) {
                case DecisionAtom.OfAnAnswer _, DecisionAtom.TakenOfAnAnswer _ -> {
                    return anAnswerARowStandsIn();
                }
                case Quantity.HowManyMeet _, Quantity.HowManyHold _ -> counted = true;
                case Quantity.HowManyDifferent _, Quantity.SumOver _,
                     Quantity.CodePointsOfAPiece _ -> overElements = true;
                case Quantity.RemainderOfADividend _ -> remainder = true;
                case Quantity.RemainderByAnInput _ -> remainderByAnInput = true;
                case Quantity.ProductOfTwo _ -> product = true;
                case Quantity.OfABinding bound -> bound.madeOf().ifPresent(past::add);
                case Quantity.WhatAnOperationAnswers _ -> answered = true;
                case DecisionAtom.OfTheInput _ -> { }
                case Quantity.HowManyCarried carried -> throw carried.reachedAReader();
            }
        }
        if (answered) {
            return forTheRun(compared, RowDemand.NoComposer.A_VALUE_AN_OPERATION_ANSWERS);
        }
        if (overElements) {
            return forTheRun(compared, RowDemand.NoComposer.A_NUMBER_OVER_ELEMENTS);
        }
        if (remainder) {
            return forTheRun(compared, RowDemand.NoComposer.A_REMAINDER_OF_A_FORM);
        }
        if (remainderByAnInput) {
            return forTheRun(compared, RowDemand.NoComposer.A_REMAINDER_BY_AN_INPUT);
        }
        if (product) {
            return forTheRun(compared, RowDemand.NoComposer.A_PRODUCT_OF_TWO_NUMBERS);
        }
        return counted ? forTheRun(compared, RowDemand.NoComposer.A_COUNT_OF_ELEMENTS)
                : forTheRun(compared, RowDemand.NoComposer.A_VALUE_THE_BODY_WORKS_OUT, past);
    }

    /**
     * {@code form met 0} as the values at two positions being one, or not — where the form weighs
     * the value at one position by one and the value at another by minus one, adds nothing, and is
     * held equal or unequal; null for any other.
     */
    private static RowDemand.OneValueAtBoth oneValueAtBoth(LinearForm<NumericTerm> form, Rel met) {
        if ((met != Rel.EQ && met != Rel.NE) || form.constant().signum() != 0
                || form.coefs().size() != 2) {
            return null;
        }
        List<TermPath> at = new ArrayList<>();
        ExactRatio sum = ExactRatio.ZERO;
        for (Map.Entry<NumericTerm, ExactRatio> each : form.coefs().entrySet()) {
            if (!(each.getKey() instanceof NumericTerm.ValueOf(TermPath position))
                    || each.getValue().abs().compareTo(ExactRatio.ONE) != 0
                    || !(sum.plus(each.getValue()) instanceof ExactAnswer.Held<ExactRatio>(
                            ExactRatio added))) {
                return null;
            }
            at.add(position);
            sum = added;
        }
        return sum.signum() == 0
                ? RowDemand.OneValueAtBoth.of(at.get(0), at.get(1), met == Rel.EQ) : null;
    }

    /**
     * A region's refusal in the words an account of the way is written in.
     *
     * <p>Two vocabularies because they answer to two readers. What a region says is about its own
     * algebra and names the term it has no order for; what an account of the way says is what an
     * author is to make of a condition that narrowed nothing. Written as one, either the region
     * would be naming conditions or the report would be reading terms.
     */
    private static WhyNotTaken whyDeclined(SearchRegion.Refusal why) {
        return switch (why) {
            case SearchRegion.Refusal.NoOrderUnderATerm _ ->
                    new WhyNotTaken.OutsideDomain(WhyNotTaken.DomainLimit.A_QUANTITY_ON_NO_ORDER);
        };
    }
}
