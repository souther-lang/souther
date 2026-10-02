package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.values.Value;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;

/**
 * How many values a declaration has, given how many the declarations it reaches have.
 *
 * <p>One step and not the answer. What every type has is settled by rising from "nothing shown" until
 * nothing moves, and this is the step that rises: handed what is known so far, it says what this one
 * declaration comes to. Kept apart from the rising so that a wrong answer is one or the other and
 * never both at once.
 *
 * <p>Every arm is an upper bound, and the one an arm may not reach for is a count of none without a
 * proof — {@link Cardinality} makes that unwritable, so the places below that name an
 * {@link Emptiness} are the whole list of ways a type comes to have none. A shape this does not decide
 * — a name that resolved to nothing, a type standing for another, a case nothing answered, a form
 * written for expressions and never for a field — answers {@link Cardinality#UNKNOWN}, because
 * refusing a declaration is what a count of none does and a shape nobody read is no reason to refuse
 * anything. The switch over types carries no {@code default} for the same reason: a form added later
 * stops the build here rather than being swallowed into whichever answer this one happened to give.
 *
 * <p>Where a declaration is shown to have none in more than one way at once, the proof it carries is
 * the nearest one and not the first one reached. Rules of its own before a position's own shape, and
 * a position's own shape before something another declaration lacks; among positions equally near,
 * the order they are declared in. So the same model gives the same proof however the reading is
 * arranged, which is what makes a refusal reproducible.
 *
 * <p>A position is read where it sits. The rules a record wrote about a field reach the value
 * standing there and are read at that field's own path, which is what makes a list holding at least
 * one a different question from the same list holding none. A value a collection holds is not that
 * position — nothing was written about it there — so the reading is put down at a collection's
 * element and the element is asked about its type alone. What that loses is precision: rules do reach
 * an element, and taking the type's answer gives a collection more distinct values to draw on than it
 * has, which admits where a narrower reading would refuse.
 */
final class CardinalityTransfer {

    /**
     * How far a collection's sizes are enumerated before the answer is given up on.
     *
     * <p>Filling a set from an element with {@code n} values means asking about every size up to
     * {@code n}, and the point of asking is to tell a small number of values from a smaller
     * collection. Past a size nothing in the model asks about, the sum is a number no comparison
     * needs, and stopping is losing precision rather than soundness.
     */
    static final int ENUMERATION_LIMIT = 16;

    private CardinalityTransfer() {}

    /**
     * What {@code def}, declared as {@code named}, comes to under {@code answers}, asking where
     * {@code reading} borrows from for what somebody has already made of the declaration's string
     * rules before building any of it.
     *
     * @param granted the declarations taken to have values whatever their own rules say. Their
     *                clauses are left out of every reading here, because a declaration said to have
     *                no value is one whose rules say so, and those rules are read wherever it is
     *                reached: a record holding it would otherwise be told it holds nothing by the
     *                very rules the supposing was about. The readings made that way are kept there
     *                and taken from there.
     */
    static Cardinality upperOf(TypeSymbol named, Hir.Def def, RuleReadingContext reading,
                               Answers answers, Supposing granted) {
        return switch (def) {
            case Hir.UnitData _ -> Cardinality.atMost(1);
            case Hir.SumData sum -> ofCases(namedCases(sum), answers);
            // A data is a declaration a module wrote. What the language gives never answers with
            // one, so a name reaching here that is not a module's is a declaration world and a
            // graph of names that have stopped agreeing.
            case Hir.Data data -> named instanceof TypeSymbol.AtModule at
                    ? ofData(at, data, reading, answers, granted)
                    : Declared.notAModules(named, data);
        };
    }

    /**
     * The declarations a sum's cases name, or null where one of them names nothing.
     *
     * <p>A case resolution found no declaration for is a case this reading never took in. It is
     * reported where it is written, and counting the sum without it would answer for a shape that
     * was never read — so the sum is answered the way every other unread shape is.
     */
    private static List<TypeSymbol> namedCases(Hir.SumData sum) {
        List<TypeSymbol> named = new ArrayList<>();
        for (Hir.Name each : sum.cases()) {
            if (!(each instanceof Hir.Name.Denoting denoting)) {
                return null;
            }
            named.add(denoting.type());
        }
        return named;
    }

    /**
     * What a sum of {@code cases}, or a union of them, comes to.
     *
     * <p>A case bottoming out is the whole sum bottoming out, so these are added: what has no value
     * adds none, and the sum has none only where every one of them has none. Read as a whole rather
     * than folded from a count of none, because "all of them" is the proof and no one of them speaks
     * for the rest.
     */
    private static Cardinality ofCases(List<TypeSymbol> cases, Answers answers) {
        if (cases == null || cases.isEmpty()) {
            return Cardinality.UNKNOWN;   // nothing here was read
        }
        List<Emptiness> without = new ArrayList<>();
        Cardinality.Standing across = null;
        for (TypeSymbol each : cases) {
            switch (answers.of(each)) {
                case Cardinality.None it -> without.add(it.why());
                case Cardinality.Standing it -> across = across == null ? it : across.plus(it);
            }
        }
        return across != null ? across : Cardinality.none(new Emptiness.AcrossEveryCase(without));
    }

    private static Cardinality ofData(TypeSymbol.AtModule named, Hir.Data data,
                                      RuleReadingContext reading, Answers answers,
                                      Supposing granted) {
        RuleReadingSource source = reading.source();
        // One reading of the rules for all three questions below, as the supposing has them.
        DeclarationReading read = granted.readingOf(named, reading);
        // Rules that cannot all hold leave nothing to count, and the ends they would have been
        // counted between are gone with them. Asked before the positions, which have nothing to say
        // about a value the declaration as a whole refuses, and nearer than anything they could say.
        Optional<Emptiness> contradiction =
                FieldDomains.of(read, reading, granted.reach())
                        .holdsNothing(reading.readings().of(named.key()));
        if (contradiction.isPresent()) {
            return Cardinality.none(contradiction.get());
        }
        OccurrenceCounts counts = OccurrenceCounts.of(read.seeded());
        OccurrenceValues values = OccurrenceValues.of(read.seeded());
        Map<String, Type> fields = TypeOps.fieldTypes(data, source.symbols());
        if (data.newtype()) {
            // A newtype is one value under a name, so its value sits where it sits: the rules written
            // on the name are about what the value holds, and the value is at no path of its own.
            Type representation = fields.get("value");
            return representation == null ? Cardinality.UNKNOWN
                    : at(RuleKey.THE_VALUE, upperAt(representation, RuleKey.THE_VALUE,
                            counts, values, source, answers, granted, new HashSet<>(Set.of(named))));
        }
        RuleKey emptiestAt = null;
        Emptiness emptiest = null;
        Cardinality.Standing across = Cardinality.atMost(1);   // a record of no fields is one value
        for (String field : TypeOps.fieldLayout(data, source.symbols())) {
            // Every field, and not up to the first one with nothing in it. Which proof the record
            // carries is settled by how near the proofs are and, where two are equally near, by
            // where the fields stand — so that is asked of what answers it rather than taken off
            // the mapping beside it, which answers what each field holds and no order at all.
            switch (upperAt(fields.get(field), RuleKey.of(field), counts, values, source,
                    answers, granted, new HashSet<>())) {
                case Cardinality.None it -> {
                    if (emptiest == null || it.why().category().compareTo(emptiest.category()) < 0) {
                        emptiest = it.why();
                        emptiestAt = RuleKey.of(field);
                    }
                }
                case Cardinality.Standing it -> across = across.times(it);
            }
        }
        return emptiest == null ? across
                : Cardinality.none(new Emptiness.AtAField(where(emptiestAt), emptiest));
    }

    /**
     * How many values {@code type} has, where they are something that can be written out.
     *
     * <p>Nothing proven where they cannot be, which is the answer every shape this does not read
     * gets. A type whose values can be written out has at least one of them: a list with nothing in
     * it is not a type, and the count of none is a claim that carries a proof.
     */
    private static Cardinality howManyValues(Type type, NewtypeInners inners,
                                             DeclarationKinds kinds,
                                             SumCases sums) {
        List<Value> every = ValueUniverse.of(type, inners, kinds, sums);
        return every == null || every.isEmpty() ? Cardinality.UNKNOWN
                : Cardinality.atMost(every.size());
    }

    /** {@code count} as it stands at {@code path}, which is where a proof of none says it sits. */
    private static Cardinality at(RuleKey path, Cardinality count) {
        return count instanceof Cardinality.None it
                ? Cardinality.none(new Emptiness.AtAField(where(path), it.why())) : count;
    }

    /** The place a proof names, said as the reading has it rather than as text a reader takes
     *  apart again. */
    private static Emptiness.AtAField.Where where(RuleKey path) {
        return path.isTheValueItself() ? new Emptiness.AtAField.Where.TheValueItself()
                : new Emptiness.AtAField.Where.In(path.toString());
    }

    /**
     * How many values may stand at one position.
     *
     * @param path  where the position sits in the value {@code counts} and {@code values} were read
     *              from
     * @param worn  the names this value is already wearing, so that a newtype reached from inside
     *              itself is answered from {@code answers} rather than unwrapped again
     */
    static Cardinality upperAt(Type type, RuleKey path, OccurrenceCounts counts,
                               OccurrenceValues values, RuleReadingSource source,
                               Answers answers, Supposing granted,
                               Set<TypeSymbol> worn) {
        return new Walk(source, answers, granted, worn).at(type, path, counts, values);
    }

    /** How many times a reading has opened a name worn over a value. */
    static long namesOpened() {
        return OPENED.get();
    }

    private static final AtomicLong OPENED = new AtomicLong();

    /**
     * What a name with {@code named} comes to once opened onto what it wraps, which came to
     * {@code unwrapped}.
     *
     * <p>Both readings bound the same values, so the narrower of them holds. Where both come to none,
     * what is left to choose is which proof is carried: the unwrapped one is about the rules written
     * at the position and the named one stops at the name, and the nearer of the two is the one that
     * says something there.
     */
    static Cardinality throughTheName(Cardinality named, Cardinality unwrapped) {
        if (named instanceof Cardinality.Standing here
                && unwrapped instanceof Cardinality.Standing there) {
            return Cardinality.Standing.narrower(here, there);
        }
        if (named instanceof Cardinality.None it && unwrapped instanceof Cardinality.None other) {
            return other.why().category().compareTo(it.why().category()) <= 0 ? other : it;
        }
        return named instanceof Cardinality.None ? named : unwrapped;
    }

    /**
     * What opening {@code named} finds beneath it, for the readings that reach it after it is
     * answered.
     *
     * <p>Where it wraps a name that was opened already, that one's opening with this name's count
     * taken on top; otherwise this name opened onto what it wraps. A name the readings never open
     * stops at its count, as {@link Walk} would.
     */
    static Unwrapping unwrappingOf(TypeSymbol named, Hir.Def def, RuleReadingSource source,
                                   Answers answers, Supposing granted) {
        Cardinality count = answers.of(named);
        if (granted.contains(named) || !(def instanceof Hir.Data data) || !data.newtype()) {
            return Unwrapping.stoppingAt(count);
        }
        Type representation = TypeOps.fieldTypes(data, source.symbols()).get("value");
        if (representation == null) {
            return Unwrapping.stoppingAt(count);
        }
        Unwrapping beneath = representation instanceof Type.Ref ref
                ? answers.unwrappingOf(ref.name()) : null;
        return beneath != null ? beneath.beneath(count)
                : Unwrapping.onto(representation, count,
                        new Walk(source, answers, granted, new HashSet<>(Set.of(named)))
                                .held(representation));
    }

    /**
     * What a collection the rules will not let hold anything comes to.
     *
     * <p>The empty collection is a value of its own, so this is one wherever the rules leave room for
     * it. Where they do not, there is nothing left for the collection to be, and which of the two
     * refusals it is depends on what left it nothing to hold: rules that admit no size at all, or an
     * element there is no value of. Both were one answer once, which is a count of none reached two
     * ways and said one way.
     */
    private static Cardinality noSizeLeft(OccurrenceCounts counts, RuleKey path) {
        return counts.mayHoldExactly(path, 0) ? Cardinality.atMost(1)
                : Cardinality.none(new Emptiness.NoAllowedCollectionSize());
    }

    private static Cardinality nothingToHold(OccurrenceCounts counts, RuleKey path,
                                             Emptiness element) {
        return counts.mayHoldExactly(path, 0) ? Cardinality.atMost(1)
                : Cardinality.none(new Emptiness.NonEmptyCollectionWithNoElement(element));
    }

    /** The sets at {@code path}, of an element with {@code each} values. */
    private static Cardinality setsOf(Cardinality.Standing each, RuleKey path,
                                      OccurrenceCounts counts) {
        long distinct = each.boundOr(-1);
        if (distinct < 0) {
            return Cardinality.UNKNOWN;
        }
        // A set holds each of its element's values once, so a size above how many there are is a size
        // nothing fills. Asked whatever the number, because it is one question and not an
        // enumeration.
        if (!counts.mayHoldAtMost(path, distinct)) {
            return Cardinality.none(new Emptiness.SetRequiresTooManyDistinctValues(distinct));
        }
        if (distinct > ENUMERATION_LIMIT) {
            return Cardinality.UNKNOWN;
        }
        Cardinality.Standing across = null;
        for (long size = 0; size <= distinct; size++) {
            if (counts.mayHoldExactly(path, size)) {
                Cardinality.Standing here = each.choose(size);
                across = across == null ? here : across.plus(here);
            }
        }
        // Nothing reaches the second of these. A collection got this far by admitting a size of one
        // or more and by not admitting one past where the walk stops, so a size it admits lies
        // inside what was walked and some step finds it — unless one position was asked two ways
        // round and the answers disagreed, which is not something this decided. Answered the way
        // every undecided shape is, because refusing a declaration is what a count of none does.
        return across == null ? Cardinality.UNKNOWN : across;
    }

    /** The lists at {@code path}, of an element with {@code each} values. */
    private static Cardinality listsOf(Cardinality.Standing each, RuleKey path,
                                       OccurrenceCounts counts) {
        // A list holds its element's values over again, so length and not the element is what bounds
        // it. Left long enough and the lists are past counting however few values the element has.
        if (counts.mayHoldAtLeast(path, ENUMERATION_LIMIT + 1L)) {
            return Cardinality.UNKNOWN;
        }
        Cardinality.Standing across = null;
        for (long length = 0; length <= ENUMERATION_LIMIT; length++) {
            if (counts.mayHoldExactly(path, length)) {
                Cardinality.Standing here = each.toThe(length);
                across = across == null ? here : across.plus(here);
            }
        }
        return across == null ? Cardinality.UNKNOWN : across;   // as in `setsOf`, and as unreachable
    }

    /**
     * One reading of a position, with what is waiting on the parts of it held here rather than on
     * the call stack.
     *
     * <p>A position is read by reading its parts, and a name worn over a value is read by opening it
     * and reading what its declaration wraps — which may be another such name, or a collection of
     * one, and so on into whatever declarations the names lead to. That is the one place a reading
     * goes from one declaration to another, and how far it goes is how far the declarations lead,
     * not how deep any one of them was written. Waiting on it on the call stack would let a long
     * enough chain or ring of declarations run out of the thread's stack, so what a module comes to
     * would depend on the thread that compiled it. Each position waiting on a part is a
     * {@link Waiting} pushed here, and the reading is a loop.
     *
     * <p>Every position is answered as the reading did when it waited on its parts on the call
     * stack: the parts are asked for in the same order, and what each position does with what its
     * part came to is the same.
     */
    private static final class Walk {

        /** A position waiting on what one of its parts comes to. */
        @FunctionalInterface
        private interface Waiting {

            /** What the position comes to, its part having come to {@code part}; null where it has
             *  asked for another part and is waiting again. */
            Cardinality resume(Cardinality part);
        }

        /** A part asked for and not yet read, and where it is read from. */
        private record Part(Type type, RuleKey path, OccurrenceCounts counts,
                            OccurrenceValues values) {}

        private final RuleReadingSource source;
        private final Answers answers;
        private final Supposing granted;
        private final Set<TypeSymbol> worn;
        private final Deque<Waiting> waiting = new ArrayDeque<>();
        private Part asked;

        Walk(RuleReadingSource source, Answers answers, Supposing granted,
             Set<TypeSymbol> worn) {
            this.source = source;
            this.answers = answers;
            this.granted = granted;
            this.worn = worn;
        }

        /** How many values may stand at {@code path}. */
        Cardinality at(Type type, RuleKey path, OccurrenceCounts counts, OccurrenceValues values) {
            return finish(begin(new Part(type, path, counts, values)));
        }

        /** How many values a value of {@code type} has where no rule is written about it. */
        Cardinality held(Type type) {
            return finish(holding(part -> part, type));
        }

        /** {@code done}, or what the reading comes to once every part asked for is read. */
        private Cardinality finish(Cardinality done) {
            Cardinality now = done;
            while (true) {
                if (now == null) {
                    Part next = asked;
                    asked = null;
                    now = begin(next);
                } else if (waiting.isEmpty()) {
                    return now;
                } else {
                    now = waiting.pop().resume(now);
                }
            }
        }

        /** Waits on the position at {@code path} with {@code then}, answering nothing yet. */
        private Cardinality ask(Waiting then, Type type, RuleKey path, OccurrenceCounts counts,
                                OccurrenceValues values) {
            waiting.push(then);
            asked = new Part(type, path, counts, values);
            return null;
        }

        /**
         * A value a collection holds, which no rule of the collection's own was written about,
         * handed to {@code then}.
         *
         * <p>Read under no rule, so a name here comes to what opening it under no rule came to when
         * it was answered, and is not opened again.
         */
        private Cardinality holding(Waiting then, Type type) {
            if (type instanceof Type.Ref ref && !granted.contains(ref.name())
                    && !worn.contains(ref.name())) {
                Unwrapping known = answers.unwrappingOf(ref.name());
                if (known != null) {
                    return then.resume(known.unruled());
                }
            }
            return ask(then, type, RuleKey.THE_VALUE, OccurrenceCounts.NOTHING_READ,
                    OccurrenceValues.NOTHING_READ);
        }

        /** What {@code part} comes to, or null where it waits on a part of its own. */
        private Cardinality begin(Part part) {
            RuleKey path = part.path();
            OccurrenceCounts counts = part.counts();
            return switch (part.type()) {
                case Type.Prim prim -> switch (prim) {
                    // As many as it has values, which is a question with an answer of its own.
                    // Written here as a number, the count and the values would be two records of one
                    // fact with nothing holding them together.
                    case BOOL -> howManyValues(part.type(), source.inners(), source.kinds(),
                            source.sums());
                    case INT -> part.values().wholeValuesAt(path);
                    // Spaced too finely to count between two ends, or not spaced at all. A string
                    // bounded in length and a date bounded at both ends are finite and are not
                    // counted here: what it would take is a reading of each carrier's own values,
                    // and nothing asks yet.
                    case STRING, DECIMAL, RATIONAL, DATE, TIME, DATETIME, INSTANT ->
                            Cardinality.UNKNOWN;
                };
                case Type.Ref ref -> opening(ref, part);
                // A `None` is a value of it whatever it wraps, so this is the one position that is
                // never empty. What it wraps is a value of its own type and nothing was written about
                // it here.
                case Type.OptionOf option -> holding(wrapped ->
                        wrapped instanceof Cardinality.Standing it
                                ? Cardinality.atMost(1).plus(it) : Cardinality.atMost(1),
                        option.element());
                case Type.ListOf list -> !counts.mayHoldAtLeast(path, 1) ? noSizeLeft(counts, path)
                        : holding(held -> switch (held) {
                            case Cardinality.None it -> nothingToHold(counts, path, it.why());
                            case Cardinality.Standing each -> listsOf(each, path, counts);
                        }, list.element());
                case Type.SetOf set -> !counts.mayHoldAtLeast(path, 1) ? noSizeLeft(counts, path)
                        : holding(held -> switch (held) {
                            case Cardinality.None it -> nothingToHold(counts, path, it.why());
                            case Cardinality.Standing each -> setsOf(each, path, counts);
                        }, set.element());
                case Type.MapOf map -> !counts.mayHoldAtLeast(path, 1) ? noSizeLeft(counts, path)
                        // Keyed by something this has not read.
                        : !Type.STRING.equals(map.key()) ? Cardinality.UNKNOWN
                        // A key is a string and there is no end of those, so a map holding anything
                        // at all holds it under more keys than can be counted. Only a map with
                        // nothing to hold is finite here, and one that must hold something has no
                        // value.
                        : holding(held -> held instanceof Cardinality.None it
                                ? nothingToHold(counts, path, it.why()) : Cardinality.UNKNOWN,
                                map.value());
                // Several values carried together, which is a product like a record's fields.
                // Written only inside a computation — a field of one is refused — so nothing in a
                // declaration reaches this, and a part with no value is carried up as it stands: the
                // parts sit at no path of their own for a proof to name.
                case Type.TupleOf tuple -> new Parts(tuple.elements()).next();
                case Type.Union union -> ofCases(List.copyOf(union.members()), answers);
                // A type standing for another, a name that resolved to nothing, a function, and the
                // two that only an expression reaches: `Nothing` is what an empty list literal's
                // element is waiting to be told, and `Never` is where an abort leaves off. None of
                // them is written in a declaration, and a count of none read off one would refuse a
                // type on the strength of a form this never decided.
                case Type.Open _, Type.Erroneous _, Type.FnOf _, Type.Nothing _, Type.Never _ ->
                        Cardinality.UNKNOWN;
            };
        }

        /**
         * A name, unwrapped while it is one this value is not already wearing.
         *
         * <p>The one place anything is learned about a name beyond what the answers say of it. A
         * sum reads its cases and a union its members, and both read the answer and nothing else;
         * here the name is opened and what it wraps is read again. So this is where a name that was
         * granted a value has to be left alone: opening it reaches the very rules and the very shape
         * that leave it without one, and the granting would be undone one step in.
         *
         * <p>Worn while what it wraps is read and not after. What the name stops is a value reached
         * from inside itself, which is a question about what this one is inside of; a value beside
         * it — another part of the same tuple — is read the same whichever part was read first.
         */
        private Cardinality opening(Type.Ref ref, Part part) {
            TypeSymbol name = ref.name();
            Cardinality named = answers.of(name);
            if (granted.contains(name)
                    || !(source.symbols().declaredNode(name) instanceof Hir.Data data)
                    || !data.newtype()
                    || !worn.add(name)) {
                return named;
            }
            OPENED.incrementAndGet();
            // Opened once already, where the name was answered: what is beneath it is the same names
            // with the same counts whoever opens it, and only what they end in is read under this
            // position's rules. Without this, every name opened here would open the whole of what it
            // wraps again, and a chain of them would be read once per link.
            Unwrapping known = answers.unwrappingOf(name);
            if (known != null && known.terminal() == null) {
                worn.remove(name);
                return known.standsFor();
            }
            // The name is not a step of the path: a rule the record wrote about this field reaches
            // what the name wraps, and reading the wrapped type without it would leave a floor
            // written here saying nothing.
            Cardinality over = known != null ? known.standsFor() : named;
            Type beneath = known != null ? known.terminal()
                    : TypeOps.fieldTypes(data, source.symbols()).get("value");
            if (beneath == null) {
                worn.remove(name);
                return named;
            }
            return ask(opened -> {
                worn.remove(name);
                return throughTheName(over, opened);
            }, beneath, part.path(), part.counts(), part.values());
        }

        /** The parts of a tuple, read one after another and taken together as a record's fields
         *  are. */
        private final class Parts implements Waiting {

            private final List<Type> elements;
            private int next;
            private Cardinality.Standing across = Cardinality.atMost(1);
            private Cardinality.None without;

            Parts(List<Type> elements) {
                this.elements = elements;
            }

            /** What the tuple comes to, or null where it waits on its next part. */
            Cardinality next() {
                return next < elements.size() ? holding(this, elements.get(next++))
                        : without != null ? without : across;
            }

            @Override
            public Cardinality resume(Cardinality part) {
                switch (part) {
                    case Cardinality.None it -> {
                        if (without == null
                                || it.why().category().compareTo(without.why().category()) < 0) {
                            without = it;
                        }
                    }
                    case Cardinality.Standing it -> across = across.times(it);
                }
                return next();
            }
        }
    }
}
