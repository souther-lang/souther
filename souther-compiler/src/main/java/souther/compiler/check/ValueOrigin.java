package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.coverage.NormalReturn;
import souther.compiler.types.ValueName;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * What an expression is made of, as the reader that looked it up found it.
 *
 * <p>Two questions were being answered by one word. Which positions a side of a comparison names is
 * about what the rule is over; whether an operation stands between those positions and the value
 * being compared is about what it would take to follow the rule back to them. They are not the same
 * question and they do not refuse each other — {@code Int.add(a, b)} names two positions and is an
 * operation's answer — so a classification that made a side one or the other had to drop whichever
 * it was not asked for, and the reason a rule went unread was picked from what was left.
 *
 * <p><b>The walk and the grammar are here; the environment's answers are the caller's.</b> Which
 * nodes hold what — an application of an operation, the language's own arithmetic, a value written
 * out — is a fact about the language, and it is read once. What a name denotes, which expression is
 * a position, and where a value that is no position came from depend on what the reader is looking
 * at, and are asked of {@link Reading}. Written twice, the two copies of this walk disagreed about
 * whether {@code y + 1} named anything (spec §example-partition).
 *
 * @param <K> what the caller calls a position
 */
public sealed interface ValueOrigin<K> {

    /**
     * Every position {@code gathering} finds in this, in the order the source wrote them, going into
     * each part once however many places reach it.
     *
     * <p>The way a question that collects positions reads an origin. A name read in several places is
     * one origin standing in several places ({@link #of(Core, Object, Reading)}), so a value in which
     * each link names the one before it twice is a graph as long as the source wrote it and a tree
     * that doubles at each link. Parts are held by identity and not by equality: equality of two
     * origins is a walk of both, which is the cost this is here to spare.
     *
     * <p>Walked on a stack of its own and not on the call stack, because how deep an origin goes is
     * as long as a chain of declarations: a record holding the one before it in a field is read as
     * one layer per declaration. And collected into one set as it goes rather than one per part,
     * because each part's set holds everything below it, and copying those up is quadratic in the
     * depth.
     *
     * <p>Which parts a question goes into is the question's, so it is asked of {@code gathering} and
     * not read off the node: what decided a choice is something a value depends on and not
     * something it came from.
     */
    default Set<K> gathered(Gathering<K> gathering) {
        Set<ValueOrigin<K>> met = Collections.newSetFromMap(new IdentityHashMap<>());
        Deque<ValueOrigin<K>> pending = new ArrayDeque<>();
        Set<K> out = new LinkedHashSet<>();
        pending.push(this);
        while (!pending.isEmpty()) {
            ValueOrigin<K> origin = pending.pop();
            // Marked when it is read and not when it is put off: a part put off behind its
            // neighbours and then reached again under an earlier one is read where it is first
            // written, which is where its positions belong in the order.
            if (!met.add(origin)) {
                continue;
            }
            switch (gathering.at(origin)) {
                case Gathering.Holds<K>(K at) -> out.add(at);
                case Gathering.Into<K>(List<ValueOrigin<K>> parts) -> {
                    for (int i = parts.size() - 1; i >= 0; i--) {
                        pending.push(parts.get(i));
                    }
                }
            }
        }
        return Collections.unmodifiableSet(out);
    }

    /**
     * What one question that collects positions reads out of an origin it meets.
     *
     * @param <K> what the caller calls a position
     */
    @FunctionalInterface
    interface Gathering<K> {

        /** What {@code origin} gives this question: a position, or the parts it goes on into. */
        Met<K> at(ValueOrigin<K> origin);

        /**
         * What a question met at one origin.
         *
         * @param <K> what the caller calls a position
         */
        sealed interface Met<K> {}

        /** A position this question collects. */
        record Holds<K>(K at) implements Met<K> {

            public Holds {
                Objects.requireNonNull(at, "a position held is one that is named");
            }
        }

        /** The parts this question goes on into, in the order they were written — none where it
         *  stops here. */
        record Into<K>(List<ValueOrigin<K>> parts) implements Met<K> {

            public Into {
                parts = List.copyOf(parts);
            }
        }
    }

    /** Every position this names, however deeply, in the order the reader met them. */
    default Set<K> positions() {
        return gathered(ValueOrigin::positionsOf);
    }

    private static <K> Gathering.Met<K> positionsOf(ValueOrigin<K> origin) {
        return switch (origin) {
            case IsAPosition<K> it -> new Gathering.Holds<>(it.at());
            case Applied<K> it -> new Gathering.Into<>(it.arguments());
            case Composed<K> it -> new Gathering.Into<>(it.parts());
            case Constructed<K> it -> new Gathering.Into<>(List.copyOf(it.fields().values()));
            case OneOf<K> it -> {
                List<ValueOrigin<K>> parts = new ArrayList<>(it.decidedBy());
                parts.addAll(it.alternatives());
                yield new Gathering.Into<>(parts);
            }
            case NoValue<K> _, Written<K> _, MadeFromAPosition<K> _, Unnameable<K> _ ->
                    new Gathering.Into<>(List.of());
        };
    }

    /** The expression is the position itself, or a number taken of it. */
    record IsAPosition<K>(K at) implements ValueOrigin<K> {

        public IsAPosition {
            Objects.requireNonNull(at, "this one names the position it is");
        }
    }

    /**
     * An operation answered this, over whatever its arguments were made of.
     *
     * <p>The arguments are kept in the order they were written and not gathered into a set. Which
     * argument a position stands at is what an operation's own statement about its result is
     * written in terms of, so {@code Date.daysBetween(a, b)} and {@code Date.daysBetween(b, a)} are
     * two origins; read off the positions alone they are one.
     */
    record Applied<K>(ValueName operation, List<ValueOrigin<K>> arguments)
            implements ValueOrigin<K> {

        public Applied {
            Objects.requireNonNull(operation, "an application names its operation");
            arguments = List.copyOf(arguments);
        }
    }

    /**
     * The language's own arithmetic over what stands under it: a sum, a difference, a scaling, a
     * value read out of a name the reader could see through.
     *
     * <p>Told apart from {@link Applied} because what would lift a reading of each is different
     * work. A form the arithmetic does not take apart asks for a wider fragment; an operation's
     * answer asks for a statement about that operation.
     */
    record Composed<K>(List<ValueOrigin<K>> parts) implements ValueOrigin<K> {

        public Composed {
            parts = List.copyOf(parts);
            if (parts.isEmpty()) {
                // Composed of nothing is not composition. An expression with nothing under it is a
                // value written out or one this reader cannot name, and both of those say so.
                throw new IllegalArgumentException("an expression composed of nothing is a leaf");
            }
        }
    }

    /**
     * A value built where it stands, as what each of its fields was given.
     *
     * <p>Told apart from {@link Composed}, which is a form this walk does not take apart. What a
     * construction builds a value out of is written where it stands, so a reader taking a field back
     * out of one is answered with the expression that field was given — the value it hands back is
     * the one it was handed, and not a value derived from it.
     *
     * <p>By the name of the field and not by where it stands among them. Which field a value was
     * given to is what a reader taking one back out has to go on, and a construction given two
     * positions is told apart by nothing else.
     *
     * @param fields what each declared field was given, in the order the construction evaluates them
     */
    record Constructed<K>(Map<String, ValueOrigin<K>> fields) implements ValueOrigin<K> {

        public Constructed {
            fields = Collections.unmodifiableMap(new LinkedHashMap<>(fields));
            if (fields.isEmpty()) {
                // A construction given nothing builds a value written where it stands, and that is
                // what such a value says of itself.
                throw new IllegalArgumentException("a construction given nothing is a leaf");
            }
        }
    }

    /**
     * A value that is one of several, and what decided which of them it is.
     *
     * <p>Told apart from {@link Composed} because the two are different relations. Everything under
     * a composition contributed to the value; the alternatives of a choice are what the value may
     * be, of which one is. A fork read as a composition puts what it turned on beside the values it
     * chooses between, and a reader asking where the value came from is answered with the position
     * that decided which value it is.
     *
     * <p><b>{@code decidedBy} contributes to dependency positions, but not to value provenance.</b>
     * Which positions the expression depends on includes what it turned on — a comparison over
     * {@code if flag then a else b} is one no reading of {@code flag} is outside of. Where its value
     * came from does not: none of the strings the value is are {@code flag}'s.
     */
    record OneOf<K>(List<ValueOrigin<K>> decidedBy, List<ValueOrigin<K>> alternatives)
            implements ValueOrigin<K> {

        public OneOf {
            decidedBy = List.copyOf(decidedBy);
            alternatives = List.copyOf(alternatives);
            if (alternatives.isEmpty()) {
                // A choice between nothing is not a choice. An expression that chooses has the
                // values it chooses between, and one of them is what it comes to.
                throw new IllegalArgumentException("a choice states what it is between");
            }
            for (ValueOrigin<K> each : alternatives) {
                if (each instanceof NoValue<K>) {
                    // A path that comes to no value is not one of the values, so it is not one of
                    // the alternatives either. Held here, it would answer for the value alongside
                    // the arms that have one, and every reader taking all of them together would
                    // be answering about a path the value never came down.
                    throw new IllegalArgumentException(
                            "a path that comes to no value is not a value this may be");
                }
            }
        }
    }

    /**
     * No value stands here: the path this is on comes to none.
     *
     * <p>Its own arm and not {@link Unnameable}, which is a value this reader has nothing to say
     * about. An arm departing with {@code unreachable} is not a value the expression may be, and
     * read as one it takes every reader that asks something of all of them down with it — what the
     * whole was made from, whether every value it may be was made by an operation. Both of those
     * are questions about the values, and this is the absence of one.
     */
    record NoValue<K>() implements ValueOrigin<K> {}

    /** A value written out where it stands. */
    record Written<K>() implements ValueOrigin<K> {}

    /**
     * A value that came from a position without being one: an element an operation handed out, and
     * whatever was made of it.
     *
     * <p>Where it came from and not which position it is. A rule about such a value is not a rule
     * about the values standing at the position it came from, and the two are told apart here so
     * that a reader asking either gets the answer to the one it asked.
     */
    record MadeFromAPosition<K>(K at) implements ValueOrigin<K> {

        public MadeFromAPosition {
            Objects.requireNonNull(at, "this one names where the value came from");
        }
    }

    /** Nothing this reader can say about it. */
    record Unnameable<K>() implements ValueOrigin<K> {}

    /** The position this is made from where it is made from one and names none, or null. Asked of
     *  the whole rather than of a part: a value made from a position is one value however many
     *  operations stand over it. */
    default K madeFrom() {
        return derivation().madeFrom();
    }

    /**
     * Whether this is a value an operation made of a position: where every value it may be is one,
     * a rule about it is one to be followed back through that operation.
     */
    default boolean madeByAnOperation() {
        return derivation().madeByAnOperation();
    }

    /**
     * Where this was made from and whether an operation made it, which are answered together because
     * the second is read off the first. Arithmetic over a value made from a position is an operation
     * made of that position, so a reading of one that started the other over at each layer of
     * arithmetic would walk what is under that layer once for every layer above it.
     *
     * @param madeFrom          the position this is made from where it is made from one and names
     *                          none, or null
     * @param madeByAnOperation whether every value this may be is one an operation made of a
     *                          position
     * @param <K>               what the caller calls a position
     */
    record Derivation<K>(K madeFrom, boolean madeByAnOperation) {}

    /**
     * What this is made from, each part answered once however many places reach it and before
     * anything that reaches it.
     *
     * <p>Answered on a stack of its own and not on the call stack, for the reason {@link #gathered}
     * is: an origin is as deep as a chain of declarations. A part is put off again until everything
     * under it is answered, and then answered from what that came to. Every part this is asked of is
     * one {@link #derivedFrom} said it reads, so none is asked before it has an answer.
     */
    private Derivation<K> derivation() {
        Map<ValueOrigin<K>, Derivation<K>> answered = new IdentityHashMap<>();
        Deque<ValueOrigin<K>> pending = new ArrayDeque<>();
        pending.push(this);
        while (!pending.isEmpty()) {
            ValueOrigin<K> origin = pending.peek();
            if (answered.containsKey(origin)) {
                pending.pop();
                continue;
            }
            boolean ready = true;
            for (ValueOrigin<K> part : derivedFrom(origin)) {
                if (!answered.containsKey(part)) {
                    pending.push(part);
                    ready = false;
                }
            }
            if (ready) {
                pending.pop();
                answered.put(origin, derivationOf(origin, answered));
            }
        }
        return answered.get(this);
    }

    /** The parts what {@code origin} is made from is read off. What decided a choice is not one of
     *  them: a choice made on what stands at a position is not a value made from it. */
    private static <K> List<ValueOrigin<K>> derivedFrom(ValueOrigin<K> origin) {
        return switch (origin) {
            case Applied<K> applied -> applied.arguments();
            case Composed<K> composed -> composed.parts();
            case Constructed<K> built -> List.copyOf(built.fields().values());
            case OneOf<K> choice -> choice.alternatives();
            case MadeFromAPosition<K> _, IsAPosition<K> _, Written<K> _, Unnameable<K> _,
                 NoValue<K> _ -> List.of();
        };
    }

    private static <K> Derivation<K> derivationOf(ValueOrigin<K> origin,
                                                  Map<ValueOrigin<K>, Derivation<K>> parts) {
        return switch (origin) {
            case MadeFromAPosition<K> from -> new Derivation<>(from.at(), true);
            case Applied<K> applied -> new Derivation<>(firstMadeFrom(applied.arguments(), parts),
                    true);
            // Arithmetic the terms do not take apart — unless what is under it came from a
            // position, which is the same rule about a value made from one with a layer of
            // arithmetic over it.
            case Composed<K> composed -> {
                K from = firstMadeFrom(composed.parts(), parts);
                yield new Derivation<>(from, from != null);
            }
            // A construction is not an operation, whatever it was given. A value an operation made
            // is followed back by reading that operation backwards; a reader that cannot take a
            // construction as a quantity has not got that to do. Reading what it was built with is
            // a separate ability.
            case Constructed<K> built ->
                    new Derivation<>(firstMadeFrom(built.fields().values(), parts), false);
            // Only where every value it could be came from the one position, and was made by an
            // operation, since the value is one of them and nothing here says which. Where one arm
            // of a choice is a position's own values or a literal, a rule about the choice is not
            // one to follow back through an operation.
            case OneOf<K> choice -> new Derivation<>(sameMadeFrom(choice.alternatives(), parts),
                    everyMadeByAnOperation(choice.alternatives(), parts));
            case IsAPosition<K> _, Written<K> _, Unnameable<K> _, NoValue<K> _ ->
                    new Derivation<>(null, false);
        };
    }

    /** The one position everything in {@code of} is made from, or null where they differ or any of
     *  them is made from none. */
    private static <K> K sameMadeFrom(List<ValueOrigin<K>> of,
                                      Map<ValueOrigin<K>, Derivation<K>> parts) {
        K agreed = null;
        for (ValueOrigin<K> each : of) {
            K from = parts.get(each).madeFrom();
            if (from == null || (agreed != null && !agreed.equals(from))) {
                return null;
            }
            agreed = from;
        }
        return agreed;
    }

    private static <K> K firstMadeFrom(Collection<ValueOrigin<K>> of,
                                       Map<ValueOrigin<K>, Derivation<K>> parts) {
        for (ValueOrigin<K> each : of) {
            K from = parts.get(each).madeFrom();
            if (from != null) {
                return from;
            }
        }
        return null;
    }

    private static <K> boolean everyMadeByAnOperation(List<ValueOrigin<K>> of,
                                                      Map<ValueOrigin<K>, Derivation<K>> parts) {
        for (ValueOrigin<K> each : of) {
            if (!parts.get(each).madeByAnOperation()) {
                return false;
            }
        }
        return true;
    }

    /**
     * What this walk asks its caller for: what depends on the reader's environment, and nothing
     * else.
     *
     * @param <K> what the caller calls a position
     * @param <E> what the caller carries as it goes inside a binding
     */
    interface Reading<K, E> {

        /** The position {@code e} is, or null where it is none. Asked of every node before anything
         *  under it, so a position names itself and what is inside it is the same position. */
        K positionOf(Core e, E at);

        /**
         * The longest of {@code p} and the projections shorter than it that is a position, or null
         * where none is: what {@link #positionOf} answers of each of them in turn, the longest first,
         * stopping at the first that is one.
         *
         * <p>One question and not one per projection, so that a reader can answer it walking the
         * names once. What it takes to name a projection grows with the projection, so asked of each
         * shorter one in turn, a projection as long as a chain of declarations costs the square of
         * that — and where the reader's positions stop short of the projection, every one of them is
         * asked.
         */
        default Along<K> positionAlong(Core.FieldProjection p, E at) {
            K here = positionOf(p, at);
            if (here != null) {
                return new Along<>(p.steps(), here);
            }
            for (Core.FieldProjection shorter : p.shorter()) {
                K there = positionOf(shorter, at);
                if (there != null) {
                    return new Along<>(shorter.steps(), there);
                }
            }
            return null;
        }

        /**
         * A position some projection's names reach.
         *
         * @param upTo the names of the projection that is the position: the projection's own, or
         *             one of the shorter chains it shares
         * @param at   the position
         * @param <K>  what the caller calls a position
         */
        record Along<K>(Core.FieldProjection.Steps upTo, K at) {

            public Along {
                Objects.requireNonNull(upTo, "a position along a projection is some of its names");
                Objects.requireNonNull(at, "and it is some position");
            }
        }

        /** The position the value {@code e} came from without being one, or null. Asked only where
         *  nothing under {@code e} is a position. */
        K madeFrom(Core e, E at);

        /** The value {@code read}'s name denotes and what to read it in, or null where the name
         *  stands for something of its own. */
        AffineForms.ReadThrough<E> readThrough(Core.Read read, E at);

        /** What {@code li}'s body is read in. */
        E inside(Core.LetIn li, E at);

        /** Where the arm {@code decidedBy} chooses is read, which is {@code at} with whatever
         *  choosing that arm binds entered — or nowhere this reading goes. */
        Opened<E> choosing(Choice.Decides decidedBy, E at);

        /**
         * Whether {@code e}, standing where {@code at} says it stands, can be evaluated to a value.
         *
         * <p>{@link NormalReturn}'s question, asked of the caller because the answer is rooted: an
         * expression read as a body of its own has every name in it free, and a name bound to
         * something that aborts is what makes the difference. Which body {@code e} stands in is
         * what the caller knows and this walk does not.
         */
        boolean answers(Core e, E at);
    }

    /**
     * Where an arm's answer is read.
     *
     * <p>Two answers and not one reading. An arm that binds nothing is read where the fork stands,
     * and so is an arm whose name a reading does not follow — and told apart by the reading they
     * come back as, the second reads a name that means something else outside the arm as though the
     * arm had opened it.
     *
     * @param <E> what the caller carries as it goes inside a binding
     */
    sealed interface Opened<E> {

        /** The reading the arm is read in, with whatever it binds entered. */
        record Entered<E>(E at) implements Opened<E> {

            public Entered {
                Objects.requireNonNull(at, "an arm that is entered is read somewhere");
            }
        }

        /** This reading does not go inside the arm, so what the arm answers is out of its reach. */
        record NotEntered<E>() implements Opened<E> {}
    }

    /** What {@code e} is made of. */
    static <K, E> ValueOrigin<K> of(Core e, E at, Reading<K, E> reading) {
        return of(e, at, reading, new BindingWalk<>());
    }

    /**
     * What {@code raw} is made of, reading each name it meets once ({@link BindingWalk}): a name
     * read twice is made of what it was given, and that is one answer however many places read it.
     * The origin a name comes to is shared by every place that reads it, so a value chain in which
     * each link names the one before it twice is as long as the source wrote it.
     */
    private static <K, E> ValueOrigin<K> of(Core raw, E at, Reading<K, E> reading,
                                            BindingWalk<ValueOrigin<K>> following) {
        Core e = Terms.asOperator(raw);
        if (e instanceof Core.FieldProjection projection) {
            return projected(projection, at, reading, following);
        }
        K here = reading.positionOf(e, at);
        if (here != null) {
            return new IsAPosition<>(here);
        }
        if (e instanceof Core.Read read) {
            AffineForms.ReadThrough<E> through = reading.readThrough(read, at);
            if (through != null && following.enter(read.binding())) {
                ValueOrigin<K> inside = following.readingOf(read.binding(), through.value(),
                        through.at(), () -> of(through.value(), through.at(), reading, following));
                following.leave(read.binding());
                return inside;
            }
            // A name standing for several values is not one this walk reads through. What may be
            // said of such a name is what all of its values support, and that is one law with one
            // owner — the arithmetic, which is asked before this walk is
            // ({@link souther.compiler.partition.ComparisonAssessment}). Answered here as well, it
            // would be a second account of it: two values agree as arithmetic and are made of
            // different things, so the two would differ about a name and the stricter would win.
            return leafOf(e, at, reading);
        }
        // The operation a call reaches, asked of {@link Terms} so that what counts as one is
        // settled where the arithmetic already settles it. A two-argument call the language has an
        // operator for is not one of these: {@link Terms#asOperator} has already turned it into the
        // arithmetic it stands for, which is what {@link Composed} is.
        // Asked before the choice below, and the call an operation defines by cases is the one
        // place the two could both answer. A rule about what such a call answered is one to be
        // followed back through the operation, which is what an application says and what a reader
        // of it acts on; which of its arguments the answer is comes from the same table and is a
        // question about the library rather than about this body.
        ValueName operation = Terms.operationOf(e);
        if (operation != null) {
            return new Applied<>(operation, partsOf(Terms.argsOf(e), at, reading, following));
        }
        if (writtenOut(e)) {
            return new Written<>();
        }
        // What a construction was given, kept under the field it was given to. Walked by its
        // children it would come back as a form nothing takes apart, and the provenance of a value
        // read back out of it would be a thing this could not state — while what it was built with
        // stands in the node.
        if (e instanceof Core.Construct construct) {
            Map<String, ValueOrigin<K>> fields = new LinkedHashMap<>();
            for (Core.FieldValue each : construct.values()) {
                fields.put(each.field(), of(each.value(), at, reading, following));
            }
            return new Constructed<>(fields);
        }
        // A field read back out of a construction is what that field was given: the same value,
        // named twice. So a rule about it is a rule about whatever that expression's value is made
        // of, and the field the reader asked for is the one it is answered about — the other fields
        // of the construction hold none of the values the rule is over.
        if (e instanceof Core.FieldAccess access) {
            ValueOrigin<K> target = of(access.target(), at, reading, following);
            if (target instanceof Constructed<K> built) {
                ValueOrigin<K> given = built.fields().get(access.field());
                if (given == null) {
                    // A construction holds every declared field and a field access names a field of
                    // the type it reads, so a field missing here is this compiler disagreeing with
                    // itself rather than a provenance nothing can state. Said as the one it is.
                    throw new IllegalStateException("a construction of " + built.fields().keySet()
                            + " was read for a field it has none of: " + access.field());
                }
                return given;
            }
            // A field of anything else is the one child this node has, read once here rather than
            // walked again below.
            return new Composed<>(List.of(target));
        }
        // What a {@code let} is made of is its body, read in the binding. The initializer is not a
        // part of the value: {@code let $x = a in 0} is zero, and reading both made a helper that
        // ignores its argument into an expression about the argument. It is reached where the body
        // reads the name, which is what {@link Reading#readThrough} answers — the same way the
        // arithmetic next door reaches it, so the two cannot come to different values for one
        // expression.
        if (e instanceof Core.LetIn li) {
            return of(li.body(), reading.inside(li, at), reading, following);
        }
        // A value that is one of several, said as the choice it is. Which several and what decides
        // each is {@link Choice}'s answer and not read off the node here: walked by its children a
        // fork comes back composed of what it turned on and what it chooses between alike, and the
        // two are not one relation.
        Choice choice = Choice.of(e);
        if (choice != null) {
            return oneOf(choice, at, reading, following);
        }
        List<Core> children = new ArrayList<>();
        Core.forEachChild(e, children::add);
        if (children.isEmpty()) {
            return leafOf(e, at, reading);
        }
        return new Composed<>(partsOf(children, at, reading, following));
    }

    /**
     * What {@code p} is made of: the rule for a field access below, asked of each of its names in
     * turn.
     *
     * <p>A projection or one shorter than it that is a position is that position, and nothing
     * under it is asked; which one is, is the reading's one answer ({@link Reading#positionAlong}).
     * Where none is, what the base is made of is read, and each name taken off it is either the
     * field a construction was given or one more value made of what it is read off — which is what
     * the accesses written out come to. Taken along the names rather than on the stack, because
     * how many there are is as long as the declarations chain.
     *
     * <p>One layer for every name past the last a construction answers, and not one per name. A
     * value made of one made of something is made of it the way the one under it is — what it is
     * made from, whether an operation made it, which positions it names — so a layer per name says
     * nothing a single layer does not, and a projection as deep as a chain of declarations would
     * hand every reader an origin as deep, to walk at each question it is asked.
     */
    private static <K, E> ValueOrigin<K> projected(Core.FieldProjection p, E at,
                                                   Reading<K, E> reading,
                                                   BindingWalk<ValueOrigin<K>> following) {
        Reading.Along<K> found = reading.positionAlong(p, at);
        if (found != null) {
            // A position is no construction, so every name above it is a value made of what it is
            // read off.
            return found.upTo() == p.steps() ? new IsAPosition<>(found.at())
                    : new Composed<>(List.of(new IsAPosition<>(found.at())));
        }
        ValueOrigin<K> origin = of(p.base(), at, reading, following);
        for (Core.FieldProjection.Step step : p.steps().inOrder()) {
            if (!(origin instanceof Constructed<K> built)) {
                return new Composed<>(List.of(origin));
            }
            ValueOrigin<K> given = built.fields().get(step.field());
            if (given == null) {
                throw new IllegalStateException("a construction of " + built.fields().keySet()
                        + " was read for a field it has none of: " + step.field());
            }
            origin = given;
        }
        return origin;
    }

    /**
     * What {@code choice} is made of: every value it may be, read where that value is written, and
     * what decided which of them it is.
     *
     * <p>Each arm in the reading its own arm opens ({@link Reading#choosing}). A {@code match}
     * arm's name stands for the value that was matched read as the case the arm selects, and an
     * attempt's name stands for what it built — neither of them is a name outside the arm, so an
     * arm read in the reading the fork stands in is one whose own answer cannot be looked up. An
     * arm a reading does not go inside comes to a value it can say nothing about, which is what
     * such an arm is to it.
     *
     * <p>Which arms are values the expression may be is asked of the reading and not read off the
     * node: an {@code unreachable} standing where a value is built takes the whole expression
     * around it with it, and an operator that stops as soon as its answer is settled answers a
     * value on some runs and not others. A choice no arm of which answers one comes to none
     * itself.
     */
    private static <K, E> ValueOrigin<K> oneOf(Choice choice, E at, Reading<K, E> reading,
                                               BindingWalk<ValueOrigin<K>> following) {
        List<Core> deciding = new ArrayList<>();
        List<ValueOrigin<K>> values = new ArrayList<>(choice.arms().size());
        for (Choice.Arm arm : choice.arms()) {
            for (Core each : decidedBy(arm.decidedBy())) {
                if (noneIs(deciding, each)) {
                    deciding.add(each);
                }
            }
            if (!reading.answers(arm.answers(), at)) {
                continue;
            }
            values.add(switch (reading.choosing(arm.decidedBy(), at)) {
                case Opened.Entered<E>(E inside) -> of(arm.answers(), inside, reading, following);
                case Opened.NotEntered<E> _ -> new Unnameable<K>();
            });
        }
        return values.isEmpty() ? new NoValue<>()
                : new OneOf<>(partsOf(deciding, at, reading, following), values);
    }

    /**
     * What one arm is chosen by, as the expressions it turns on.
     *
     * <p>An arm per way of deciding, so a way added to the language stops here until somebody says
     * what it turns on. What this answers is which expressions a reading of the choice depends on;
     * what choosing an arm binds and what it settles are the other two questions about the same
     * node, and each is answered where its own vocabulary is.
     */
    private static List<Core> decidedBy(Choice.Decides decidedBy) {
        return switch (decidedBy) {
            case Choice.Decides.ACondition(Core cond, boolean _) -> List.of(cond);
            case Choice.Decides.ACase(Core.Case _, Core scrutinee) -> List.of(scrutinee);
            // What the attempt tried to build is what its invariant was tested on, whichever way
            // the test went.
            case Choice.Decides.ItWasBuilt(Core.IfConstructed attempt) ->
                    List.of(attempt.construct());
            case Choice.Decides.ItDeparted(Core.IfConstructed attempt, Core.ElseArm _) ->
                    List.of(attempt.construct());
            // The values the arguments stand between, which is what the library's own definition
            // reads to say which case it answers in.
            case Choice.Decides.ByArgumentRelations(List<Choice.ArgumentRelation> relations) -> {
                List<Core> out = new ArrayList<>(relations.size() * 2);
                for (Choice.ArgumentRelation each : relations) {
                    out.add(each.left());
                    out.add(each.right());
                }
                yield out;
            }
        };
    }

    /** Whether {@code of} holds no node that is {@code e}. The same expression decides every arm of
     *  a fork, and read once it is walked once. */
    private static boolean noneIs(List<Core> of, Core e) {
        for (Core each : of) {
            if (each == e) {
                return false;
            }
        }
        return true;
    }

    private static <K, E> List<ValueOrigin<K>> partsOf(List<Core> of, E at, Reading<K, E> reading,
                                                       BindingWalk<ValueOrigin<K>> following) {
        List<ValueOrigin<K>> out = new ArrayList<>();
        for (Core each : of) {
            out.add(of(each, at, reading, following));
        }
        return out;
    }

    /**
     * Whether {@code e} is a value written where it stands.
     *
     * <p>Every one of them and not the four with a number or a string in them. A temporal is a
     * literal by {@link Core}'s own account, and a data with no fields is a value written where a
     * value goes; left out, each was a node this could say nothing about — which reads the same as
     * a value it could not reach, and they are not the same thing.
     */
    private static boolean writtenOut(Core standing) {
        Core e = Core.withoutStanding(standing);
        return e instanceof Core.Int || e instanceof Core.Decimal || e instanceof Core.Str
                || e instanceof Core.Bool || e instanceof Core.Temporal
                || e instanceof Core.UnitValue;
    }

    /** What a node nothing composes comes to: where its value came from, or nothing said. */
    private static <K, E> ValueOrigin<K> leafOf(Core e, E at, Reading<K, E> reading) {
        K from = reading.madeFrom(e, at);
        return from == null ? new Unnameable<>() : new MadeFromAPosition<>(from);
    }

}
