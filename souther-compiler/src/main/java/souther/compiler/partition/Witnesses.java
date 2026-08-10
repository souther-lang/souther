package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Values built to hold what a rule says a value must hold.
 *
 * <p>What stands for a type used to come from the carrier alone — the empty one for every collection,
 * one character for a string — and a rule saying the collection is not empty is then the one rule that
 * refuses the one value on offer. Read the minimum before the value is chosen and it is instead the
 * size the value is built at.
 *
 * <p>Proposals, and every one of them. Nothing here decides whether a newtype accepts what it is
 * handed: that is the decoder's answer and it is asked afterwards, which is what lets a value be built
 * from the part of a rule this can read while the rest of the rule refuses it. A position offering one
 * value is exactly the defect this is about, so a value built around another carries every proposal the
 * inner one made — a format and a minimum reaching the decoder separately at a position is a choice
 * that has to keep reaching it from inside a collection.
 *
 * <p>Which is why a map's key and value meet each other. They are two parts of one value and the
 * search around this is over the behavior's positions, so a key at its second proposal beside a value
 * at its first is a map nothing outside here can arrive at. Nearest first, so that a search which stops
 * has walked the low proposals of both rather than every one of the key's against the value's first.
 *
 * <p>What is bounded is what this invents rather than what it read. A set's second element and a map's
 * second key are variations made up to tell values apart, and they stop as soon as there are enough;
 * the count a rule asked for stops being worth building long before a row carrying it is one anybody
 * would read. Nothing prunes a candidate some rule was read to produce — the search that walks them is
 * bounded and says so when it stops, which is the honest place for a limit.
 *
 * <p>A tree, because a collection holds values that have rules of their own, and what stands for a list
 * of a newtype is what stands for that newtype in a list. That question is the one the position itself
 * asked, so it is asked of the same chooser. A type written in terms of itself would ask it forever, so
 * the names being expanded are carried down and a name met twice is given up on — which is the right
 * answer there, since no value of such a type exists.
 */
final class Witnesses {

    /** How many elements a proposed collection is worth building. A row is offered for somebody to read
     * and complete, and a minimum past this asks for one nobody would. */
    private static final int MOST_ELEMENTS = 64;

    /** How many characters a proposed string is worth building. Its own number, because a string of
     * sixty-five is one literal where a collection of sixty-five is sixty-five values each built in
     * turn — holding the two to one figure bounds a string by something about collections. */
    private static final int MOST_CHARACTERS = 4096;

    /** How many pairings of what a map's key and value propose are built at once. Every pair is built
     * before any of them is tried, so this bounds what is allocated rather than what is walked. */
    private static final int MOST_PAIRINGS = 64;

    /**
     * Values of a count, and whether they are all the values of it there were.
     *
     * <p>Two halves of one answer. A caller reading only the first says every value was refused where
     * some were never built, which is a different thing to tell an author and a different thing for a
     * measure to record.
     */
    record Sized(List<FixtureTemplate> values, Generator.UnresolvedCombination.Reason heldBack) {

        Sized {
            values = List.copyOf(values);
        }

        static Sized all(List<FixtureTemplate> values) {
            return new Sized(values, null);
        }
    }

    /**
     * Values of {@code carrier} whose count is exactly {@code size}, or none where this can build none.
     *
     * <p>The narrower of the two promises about a count. A caller holding a line drawn on one needs
     * the count itself and not a value that merely clears it: a row at {@code String.length = 5} is a
     * row carrying five characters, and four or six is a row at some other edge. {@link #holding}
     * reads the same build for what it asks, and neither is written in terms of the other.
     *
     * <p>Which is why nothing is the answer at a size of none and the empty value is the answer at a
     * size of zero. A rule asking a collection to hold at least none of anything has asked for no
     * value in particular; a line drawn at zero is the edge the empty one stands on, and it is a
     * value like any other.
     *
     * <p>And why what was built is counted rather than taken on trust. A set of three is three values
     * no two of which are equal, which a type of two values has not got; the two that exist are a
     * proposal for a floor and are not the count asked for here, and offering them would put a row of
     * two under a line drawn at three.
     */
    static Sized ofSize(Type carrier, int size, Symbols symbols, Set<TypeName> expanding) {
        if (size == 0) {
            return Sized.all(carrier == Type.STRING ? List.of(FixtureTemplate.string(""))
                    : carrier instanceof Type.ListOf || carrier instanceof Type.SetOf
                            || carrier instanceof Type.MapOf
                                    ? List.of(FixtureTemplate.collection(List.of())) : List.of());
        }
        Built built = sized(carrier, size, symbols, expanding);
        return new Sized(built.exactly(size), built.heldBack());
    }

    /**
     * Why no value of {@code carrier} counting exactly {@code size} was built, or null where one was.
     *
     * <p>The same decision {@link #ofSize} reads, asked for its other half, so that what could not be
     * built and why are one answer given twice rather than two answers that may disagree. Whenever
     * that one offers nothing this names a reason: a caller left to supply its own default for the
     * silence would be deciding again what this is here to answer.
     */
    static Generator.UnresolvedCombination.Reason reasonForSize(Type carrier, int size,
                                                                Symbols symbols) {
        Sized made = ofSize(carrier, size, symbols, Set.of());
        if (!made.values().isEmpty()) {
            return null;
        }
        return made.heldBack() == null
                ? Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE : made.heldBack();
    }

    /**
     * Values of {@code carrier} holding at least {@code least} of whatever counts it, or none where
     * this can build none.
     *
     * <p>The minimum itself and not one element. Recognising {@code >= 3} and then offering a list of
     * one would refuse the row for the reason the empty list was refused, having read the rule and not
     * used it.
     *
     * <p>So a value is built at the minimum, and a value short of it is offered too where the type has
     * no more to give: it is the value the rule refuses, put to the decoder so that the refusal is the
     * decoder's and is said in its terms. Both of those are this method's reading of the build, not
     * {@link #ofSize}'s — a caller with a line to stand on takes that one, where a set the type has
     * too few values for comes back as nothing at all. The two read one build and neither is written
     * in terms of the other, so a cheaper value for a floor cannot move a line.
     */
    static List<FixtureTemplate> holding(Type carrier, int least, Symbols symbols,
                                         Set<TypeName> expanding) {
        return least <= 0 ? List.of() : sized(carrier, least, symbols, expanding).all();
    }

    /**
     * Why a value of {@code carrier} holding {@code least} was not built in full, or null where it was.
     *
     * <p>The same decision {@link #holding} reads, asked for its other half. Written once because the
     * two have to agree: a reader was told a search stopped short of pairings nothing had asked to
     * build, back when this was a second reading of the same conditions.
     *
     * <p>Not {@link #reasonForSize}, for the same reason the two halves above are not one method. A
     * floor nothing was built for is a position offering what it ordinarily offers, and naming a
     * reason there would put "nothing composes one" under every position that has no floor at all.
     */
    static Generator.UnresolvedCombination.Reason heldBackFor(Type carrier, int least, Symbols symbols) {
        return least <= 0 ? null : sized(carrier, least, symbols, Set.of()).heldBack();
    }

    /**
     * A value that was built, and how many of whatever counts it it turned out to hold.
     *
     * <p>Carried rather than assumed. A string of five characters is built by writing five and a list
     * of five by repeating one, but a set of five is five values no two of which are equal and the
     * type may not have five — so what was asked for and what was made are two numbers, and only the
     * caller that needs them equal is entitled to require it.
     */
    private record Made(FixtureTemplate value, int count) {}

    /** What a value of {@code carrier} counting {@code size} comes to: what was built, and what was
     * not. */
    private record Built(List<Made> proposals,
                         Generator.UnresolvedCombination.Reason heldBack) {

        static final Built NONE = new Built(List.of(), null);

        static Built of(List<Made> proposals) {
            return new Built(List.copyOf(proposals), null);
        }

        /** Those holding exactly {@code size}, which is what a line drawn at a count is met by. */
        List<FixtureTemplate> exactly(int size) {
            return proposals.stream().filter(each -> each.count() == size)
                    .map(Made::value).toList();
        }

        /** All of them, which is what a floor to clear is offered: one short of the floor is a value
         * the decoder refuses for the reason the floor was written, and that is an answer. */
        List<FixtureTemplate> all() {
            return proposals.stream().map(Made::value).toList();
        }
    }

    private static Built sized(Type carrier, int least, Symbols symbols, Set<TypeName> expanding) {
        if (carrier == null || least <= 0) {
            return Built.NONE;
        }
        // A string is counted by its characters, and one character is as good as another where the
        // rule is about how many there are. What a format asks for instead is a proposal of its own,
        // put beside this one by the caller.
        if (carrier == Type.STRING) {
            return least > MOST_CHARACTERS
                    ? new Built(List.of(), Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE)
                    : Built.of(List.of(new Made(FixtureTemplate.string("x".repeat(least)), least)));
        }
        if (!(carrier instanceof Type.ListOf || carrier instanceof Type.SetOf
                || carrier instanceof Type.MapOf)) {
            return Built.NONE;
        }
        if (least > MOST_ELEMENTS) {
            return new Built(List.of(),
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        // A list may hold the same element as many times as it needs to.
        if (carrier instanceof Type.ListOf list) {
            List<Made> out = new ArrayList<>();
            for (FixtureTemplate each : proposalsFor(list.element(), symbols, expanding)) {
                List<FixtureTemplate> elements = new ArrayList<>();
                for (int i = 0; i < least; i++) {
                    elements.add(each);
                }
                out.add(new Made(FixtureTemplate.collection(elements), elements.size()));
            }
            return Built.of(out);
        }
        // A set of three is three elements no two of which are equal, and a map of three is three
        // entries no two of which share a key. The values under a map's keys are free to repeat.
        if (carrier instanceof Type.SetOf set) {
            List<Made> out = new ArrayList<>();
            for (FixtureTemplate seed : proposalsFor(set.element(), symbols, expanding)) {
                List<FixtureTemplate> elements =
                        distinctFrom(seed, set.element(), least, symbols, expanding);
                out.add(new Made(FixtureTemplate.collection(elements), elements.size()));
            }
            return Built.of(out);
        }
        Type.MapOf map = (Type.MapOf) carrier;
        List<FixtureTemplate> keys = proposalsFor(map.key(), symbols, expanding);
        List<FixtureTemplate> values = proposalsFor(map.value(), symbols, expanding);
        if (keys.isEmpty() || values.isEmpty()) {
            return Built.NONE;
        }
        List<Made> out = new ArrayList<>();
        // Every pair, nearest first. A key's rules and a value's are answered together or not at all —
        // the pair is inside one position, so no search outside can put a key's second proposal beside
        // a value's first — and taking them in step would offer only the pairs whose two proposals
        // happen to have been read in the same order. Nearest first is what makes the bound below cost
        // the least: what it drops is the pairs furthest from what either side proposed first.
        for (int apart = 0;
                apart <= keys.size() + values.size() - 2 && out.size() < MOST_PAIRINGS; apart++) {
            for (int i = Math.max(0, apart - values.size() + 1);
                    i <= Math.min(apart, keys.size() - 1) && out.size() < MOST_PAIRINGS; i++) {
                FixtureTemplate value = values.get(apart - i);
                List<FixtureTemplate> entries = new ArrayList<>();
                for (FixtureTemplate key
                        : distinctFrom(keys.get(i), map.key(), least, symbols, expanding)) {
                    entries.add(FixtureTemplate.entry(key, value));
                }
                out.add(new Made(FixtureTemplate.collection(entries), entries.size()));
            }
        }
        return new Built(out, keys.size() * values.size() > out.size()
                ? Generator.UnresolvedCombination.Reason.SEARCH_LIMIT : null);
    }

    /**
     * What the position at {@code type} would itself be offered, which is what a value built around it
     * has to keep offering.
     *
     * <p>All of them. Each is what one rule was read to produce — the shortest string a format accepts,
     * a string of the length a minimum asks for, the value the carrier stands for — so a budget over
     * this list drops a candidate on the strength of how many rules were read before it. The minimum's
     * is added last of those, which is exactly the one such a budget takes away.
     */
    private static List<FixtureTemplate> proposalsFor(Type type, Symbols symbols,
                                                      Set<TypeName> expanding) {
        return Partitions.representativesOf(type, symbols, null, expanding);
    }

    /**
     * {@code seed} and up to {@code least} values in all, no two of them equal.
     *
     * <p>Fewer than asked where the type runs out, which is not the same as failing: a set of three
     * booleans is a thing no value satisfies, and offering the two that exist is a proposal the decoder
     * answers the way it answers any other.
     */
    private static List<FixtureTemplate> distinctFrom(FixtureTemplate seed, Type type, int least,
                                                      Symbols symbols, Set<TypeName> expanding) {
        Set<String> written = new LinkedHashSet<>();
        List<FixtureTemplate> out = new ArrayList<>();
        written.add(seed.text());
        out.add(seed);
        // One more than needed, since the seed is likely to be among them.
        for (FixtureTemplate each : distinctValuesOf(type, least + 1, symbols, expanding)) {
            if (out.size() >= least) {
                break;
            }
            if (written.add(each.text())) {
                out.add(each);
            }
        }
        return List.copyOf(out);
    }

    /**
     * Up to {@code many} values of {@code type}, no two of them equal.
     *
     * <p>One place that answers what a type's values are, in the order a collection should reach for
     * them. Written once because it was written three times: a set of a carrier this could not step was
     * offered one element, and adding a carrier meant remembering every reader that walked one.
     *
     * <p>What the type divides into comes first. A {@code Bool} is two values and a sum is its cases,
     * and each of those is a value of the type rather than a proposal about it — a set of two booleans
     * is built from both of them or from nothing. Then values made by stepping the carrier, which stay
     * inside the rules the type carries. The type's own proposals come last: each is what one rule
     * asked for and any of them may be one the whole of the rules refuses, so a collection filled from
     * them is refused for its elements — which is still better than a collection short of its size,
     * and is all there is where the carrier neither divides nor steps.
     */
    private static List<FixtureTemplate> distinctValuesOf(Type type, int many, Symbols symbols,
                                                          Set<TypeName> expanding) {
        Set<String> written = new LinkedHashSet<>();
        List<FixtureTemplate> out = new ArrayList<>();
        for (FixtureTemplate each : dividesInto(type, symbols)) {
            if (out.size() >= many) {
                return List.copyOf(out);
            }
            if (written.add(each.text())) {
                out.add(each);
            }
        }
        for (int i = 0; out.size() < many; i++) {
            FixtureTemplate each = varied(type, i, symbols);
            if (each == null) {
                break;
            }
            if (written.add(each.text())) {
                out.add(each);
            }
        }
        for (FixtureTemplate each : Partitions.representativesOf(type, symbols, null, expanding)) {
            if (out.size() >= many) {
                break;
            }
            if (written.add(each.text())) {
                out.add(each);
            }
        }
        return List.copyOf(out);
    }

    /** The values a type divides into, under every name it wears: a {@code Bool} is two of them and a
     * sum is its cases. Empty where the type is not divided, which is where a range or a length is
     * what tells its values apart instead. */
    private static List<FixtureTemplate> dividesInto(Type type, Symbols symbols) {
        List<FixtureTemplate> out = new ArrayList<>();
        for (PartitionClass each : Partitions.classesOf(type, symbols)) {
            if (each.generatable()) {
                out.addAll(each.representatives().candidates());
            }
        }
        if (!out.isEmpty()) {
            return out;
        }
        // A newtype divides where what it wraps does, and the values are written under its name.
        Type carrier = TypeOps.base(type, symbols);
        if (carrier == null || carrier.equals(type)) {
            return List.of();
        }
        for (PartitionClass each : Partitions.classesOf(carrier, symbols)) {
            if (each.generatable()) {
                for (FixtureTemplate value : each.representatives().candidates()) {
                    out.add(wrapped(type, value, symbols));
                }
            }
        }
        return out;
    }

    /**
     * The {@code index}th value of {@code type} made by stepping its carrier, or null where the carrier
     * has no order to step.
     *
     * <p>A string grows by a character from the length its rules ask for, and a whole number steps
     * through the range they leave. A date or a record has no such step that keeps every rule the
     * position carries, and inventing one would put a value in a row the type's own chooser had reason
     * not to offer — which is what the values a type divides into are for, above.
     */
    private static FixtureTemplate varied(Type type, int index, Symbols symbols) {
        Type carrier = TypeOps.base(type, symbols);
        if (carrier == Type.STRING) {
            return wrapped(type, FixtureTemplate.string(
                    "x".repeat(Math.max(1, Partitions.leastHeld(type, symbols)) + index)), symbols);
        }
        BigDecimal number = Partitions.numberInside(type, symbols, index);
        if (number == null) {
            return null;
        }
        return wrapped(type, carrier == Type.DECIMAL ? FixtureTemplate.decimal(number)
                : FixtureTemplate.integer(number.longValueExact()), symbols);
    }

    /** The value under every name the position wears, which is how it is written where the position
     * declares a newtype rather than what the newtype carries. */
    static FixtureTemplate wrapped(Type type, FixtureTemplate bare, Symbols symbols) {
        if (!(type instanceof Type.Ref ref) || !(symbols.get(ref.name()) instanceof Ast.Data data)
                || !data.newtype()) {
            return bare;
        }
        TypeName name = ref.name();
        return FixtureTemplate.newtype(name,
                wrapped(TypeOps.newtypeInner(name, symbols), bare, symbols));
    }

    private Witnesses() {}
}
