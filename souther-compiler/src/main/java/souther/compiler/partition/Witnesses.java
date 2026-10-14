package souther.compiler.partition;

import souther.compiler.ast.Hir;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.ElementsApart;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.values.ValueSet;
import souther.compiler.revision.RevisionKnowledge;
import souther.compiler.revision.RevisionWork;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.types.ApplicationOrigin;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;

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

    private static final int MOST_PAIRINGS =
            CompositionBudget.PAIRINGS_BUILT_AT_ONCE.maximum();

    /**
     * Values of {@code position} whose count is exactly {@code size}, or none where this can build
     * none, with what of this compiler's the build met.
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
     *
     * @param held what the rules of the value holding this one keep its elements apart at
     *             ({@link ElementsKeptApart#heldBy}), nothing where nothing holds it
     */
    static Proposals ofSize(TypeView position, int size, List<List<String>> held,
                            RuleReadingContext reading, Set<TypeSymbol> expanding) {
        Shape carrier = position.shape();
        if (size == 0) {
            // The same shapes {@link #sized} builds for, and for the same reason they are written
            // out: what a value of none looks like is a question about each shape.
            return Proposals.of(switch (carrier) {
                case Shape.Scalar scalar when scalar.prim() == Type.Prim.STRING ->
                        List.of(FixtureTemplate.string(""));
                case Shape.Sequence _, Shape.Mapping _ ->
                        List.of(FixtureTemplate.collection(List.of()));
                case Shape.Scalar _, Shape.Product _, Shape.Sum _, Shape.Unit _, Shape.Optional _,
                     Shape.Unresolved _, Shape.Cases _, Shape.Tuple _, Shape.Function _,
                     Shape.Uninhabited _, Shape.Bottom _, Shape.Erroneous _,
                     Shape.Undecided _ -> List.<FixtureTemplate>of();
            });
        }
        return sized(position, size, held, reading, expanding).exactly(size);
    }

    /**
     * Why no value of {@code position} counting exactly {@code size} was built, or null where one
     * was.
     *
     * <p>The same decision {@link #ofSize} reads, asked for its other half, so that what could not be
     * built and why are one answer given twice rather than two answers that may disagree. Whenever
     * that one offers nothing this names a reason: a caller left to supply its own default for the
     * silence would be deciding again what this is here to answer.
     *
     * <p>The word and not which budget it was. A budget that stopped this is the build's own answer
     * ({@link Proposals#met()}) and travels as itself; what is here is the word a search comes back
     * with, for readers that have only ever wanted that.
     */
    static Generator.UnresolvedCombination.Reason reasonForSize(TypeView position, int size,
                                                                RuleReadingContext reading) {
        Proposals made = ofSize(position, size, List.of(), reading, Set.of());
        if (!made.isEmpty()) {
            return null;
        }
        return made.met().figures().isEmpty()
                ? Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE
                : Generator.UnresolvedCombination.Reason.wordFor(made.met().figures());
    }

    /**
     * What to put to the decoder at a position a rule gives a floor of {@code least}, or nothing where
     * this can build nothing.
     *
     * <p>Proposals and not witnesses, which is the whole of the difference from {@link #ofSize}. What
     * comes back holds the floor where the type has that much to give and falls short of it where the
     * type does not, and either way it is the decoder that answers — so a caller reading this as
     * "values of at least {@code least}" is reading a promise nothing here makes.
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
     *
     * <p>Not {@link #reasonForSize} for what it met, for the same reason the two are not one method.
     * A floor nothing was built for is a position offering what it ordinarily offers, and naming a
     * reason there would put "nothing composes one" under every position that has no floor at all;
     * what it carries is the figures the build was stopped by, which a reader of the offer weighs.
     *
     * @param held what the rules of the value holding this one keep its elements apart at, as
     *             {@link #ofSize} takes it
     */
    static Proposals holding(TypeView position, int least, List<List<String>> held,
                             RuleReadingContext reading, Set<TypeSymbol> expanding) {
        if (least <= 0) {
            return Proposals.NONE;
        }
        return sized(position, least, held, reading, expanding).all();
    }

    /** One step of building values at a count: a value made, or one a figure stopped. */
    private sealed interface Step {}

    /**
     * A value that was built, and how many of whatever counts it it turned out to hold.
     *
     * <p>Carried rather than assumed. A string of five characters is built by writing five and a list
     * of five by repeating one, but a set of five is five values no two of which are equal and the
     * type may not have five — so what was asked for and what was made are two numbers, and only the
     * caller that needs them equal is entitled to require it.
     */
    private record Made(FixtureTemplate value, int count) implements Step {}

    /** A value not made there, and what of this compiler's stopped it: one of its elements'
     *  values, or the count itself. */
    private record Halted(CompositionShortfall met) implements Step {}

    /** What a value of the position counting {@code size} comes to: what was built and where the
     * build was stopped, in the order it came to them. */
    private record Built(List<Step> steps) {

        static final Built NONE = new Built(List.of());

        Built {
            steps = List.copyOf(steps);
        }

        static Built of(List<Made> made) {
            return new Built(List.copyOf(made));
        }

        static Built stoppedBy(CompositionBudget budget) {
            return new Built(List.of(new Halted(CompositionShortfall.of(List.of(budget)))));
        }

        /** Those holding exactly {@code size}, which is what a line drawn at a count is met by. */
        Proposals exactly(int size) {
            return kept(size);
        }

        /** All of them, which is what a floor to clear is offered: one short of the floor is a value
         * the decoder refuses for the reason the floor was written, and that is an answer. */
        Proposals all() {
            return kept(-1);
        }

        /** Those holding {@code size}, or all where it is negative, with the stops where they stood. */
        private Proposals kept(int size) {
            Proposals.Gathering out = Proposals.Gathering.inOrder();
            for (Step each : steps) {
                switch (each) {
                    case Made made when size < 0 || made.count() == size -> out.add(made.value());
                    case Made _ -> { }
                    case Halted(CompositionShortfall met) -> out.stop(met);
                }
            }
            return out.done();
        }
    }

    /**
     * The figure a value holding {@code count} elements is past, or null where it is inside it.
     *
     * <p>The one place a value built here is held to how many it holds, and every reader that
     * decides how many a value it builds holds asks it before building one: the value built at a
     * count, every content a collection is walked through, and a collection filled to what its
     * rules ask. Asked by one of them alone, the others built at whatever count the rules asked
     * for, so a collection past the figure was refused at one door and built at the next. Past it,
     * a value is one this compiler does not build, which is not one the model cannot have.
     */
    private static CompositionBudget pastTheElements(int count) {
        return count > CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS.maximum()
                ? CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS : null;
    }

    /** The same, of a string holding {@code count} characters. */
    private static CompositionBudget pastTheCharacters(int count) {
        return count > CompositionBudget.CHARACTERS_A_PROPOSAL_HOLDS.maximum()
                ? CompositionBudget.CHARACTERS_A_PROPOSAL_HOLDS : null;
    }

    private static Built sized(TypeView position, int least, List<List<String>> held,
                               RuleReadingContext reading, Set<TypeSymbol> expanding) {
        if (least <= 0) {
            return Built.NONE;
        }
        // Exhaustive over what a position can be, with no `default`. Whether a value of a shape
        // counts anything is a question about each of them, and a chain of tests answers "no" for a
        // shape added later without being asked.
        return switch (position.shape()) {
            // A string is counted by its characters. Which characters is a question the count does
            // not answer, so what the position's own rules admit of that many comes first and a
            // string of any characters at all after it — both are proposals, and the one every rule
            // admits is the one a caller with a single chance needs.
            case Shape.Scalar scalar when scalar.prim() == Type.Prim.STRING ->
                    pastTheCharacters(least) != null
                            ? Built.stoppedBy(pastTheCharacters(least))
                            : Built.of(ofThatManyCharacters(position, least, reading));
            case Shape.Sequence sequence -> pastTheElements(least) != null
                    ? Built.stoppedBy(pastTheElements(least))
                    : ofSequence(sequence, ElementsKeptApart.at(position, held, reading), least,
                            reading, expanding);
            case Shape.Mapping mapping -> pastTheElements(least) != null
                    ? Built.stoppedBy(pastTheElements(least))
                    : ofMapping(mapping, least, reading, expanding);
            // Nothing else has a count this builds to. A number is one value however many the rules
            // ask for, a record holds its fields and not a number of them, and the shapes that are
            // not value shapes have no value to count.
            case Shape.Scalar _, Shape.Product _, Shape.Sum _, Shape.Unit _, Shape.Optional _,
                 Shape.Unresolved _, Shape.Cases _, Shape.Tuple _, Shape.Function _,
                 Shape.Uninhabited _, Shape.Bottom _, Shape.Erroneous _,
                 Shape.Undecided _ -> Built.NONE;
        };
    }

    /**
     * Strings of exactly {@code least} characters: the one the position's rules admit, and the one
     * any string of that many is.
     *
     * <p>Both, and in that order. What a string of that length looks like is a question about
     * strings and is the same answer for every position — which is why the second is always here,
     * and why what this reports when nothing builds stays a claim about strings rather than an
     * opinion about one type. The first is that answer narrowed by what the position's own rules
     * say its strings are, which is a value the decoder can accept where the second is one a format
     * refuses.
     */
    private static List<Made> ofThatManyCharacters(TypeView position, int least,
                                                   RuleReadingContext reading) {
        List<Made> out = new ArrayList<>();
        for (FixtureTemplate each : Partitions.admittedStringOfSize(position, reading, least)) {
            out.add(new Made(each, least));
        }
        out.add(new Made(FixtureTemplate.string("x".repeat(least)), least));
        return out;
    }

    /**
     * A list or a set of that many, around each value the element is itself offered.
     *
     * <p>Elements free to repeat are that value as many times as it takes. Elements to be apart
     * ({@code apart}, as {@link ElementsApart} reads them) are that value and others apart from it
     * and from each other, which the values there have to supply — fewer than asked where they run
     * out, which is not the same as failing: a set of three booleans is a thing no value satisfies,
     * and offering the two that exist is a proposal the decoder answers the way it answers any
     * other.
     */
    private static Built ofSequence(Shape.Sequence carrier, List<List<String>> apart, int least,
                                    RuleReadingContext reading, Set<TypeSymbol> expanding) {
        List<Step> out = new ArrayList<>();
        // What the others may be is a question about the element and the count and not about the
        // value they are built around, so it is answered once for every one of them: the values at
        // each run, as many as a container held around one value passes over, and each element
        // made of them as it is first asked for.
        ElementsMadeApart others = apart.isEmpty() ? null
                : ElementsMadeApart.of(carrier.element(), apart, least + 2, reading,
                        expanding);
        // One container around each value the element is offered, and where the element's offer
        // was stopped, a container not built there: a set short of its size because the element's
        // values were cut at a figure is that figure's doing. And each container says what the
        // values it was filled from met in front of the ones it took.
        for (Proposals.Entry entry : proposalsFor(carrier.element(), reading, expanding)
                .entries()) {
            switch (entry) {
                case Proposals.Stopped(CompositionShortfall met) -> out.add(new Halted(met));
                case Proposals.Offered(FixtureTemplate seed) -> {
                    List<FixtureTemplate> elements = new ArrayList<>();
                    if (others == null) {
                        for (int i = 0; i < least; i++) {
                            elements.add(seed);
                        }
                    } else {
                        // One value held is equal to no other held, so this always builds.
                        Around filled = others.around(List.of(seed), Set.of(), least);
                        if (!filled.met().nothing()) {
                            out.add(new Halted(filled.met()));
                        }
                        elements.addAll(filled.elements());
                    }
                    out.add(new Made(FixtureTemplate.collection(elements), elements.size()));
                }
            }
        }
        return new Built(out);
    }

    /**
     * A list or a set of {@code position} holding exactly {@code size} elements no two of which
     * are equal at the end of {@code fields} — each a run of fields taken from the element, empty
     * for the element itself — or nothing where that cannot be built: the values there have too few,
     * a field on the way is no field of a record this writes, or it is no list or set.
     *
     * <p>For a caller that needs its elements told apart at what another container is asked about
     * — a container whose elements are to be on two sides of a statement that container decides —
     * and not a proposal for any container of that size, which may say one value again. Apart at
     * those positions and not merely as whole values: two records equal at the one field the
     * statement reads are one element to it however the rest of them differ.
     *
     * <p>And apart wherever the rules ask it to be — its own names', and {@code held}, those of the
     * value holding it ({@link ElementsKeptApart#heldBy}) — since those hold of every container
     * built there whatever a caller needed it for.
     */
    static Proposals apart(TypeView position, int size, List<List<String>> fields,
                           List<List<String>> held, RuleReadingContext reading) {
        if (!(position.shape() instanceof Shape.Sequence carrier)) {
            return Proposals.NONE;
        }
        if (size == 0) {
            return Proposals.of(List.of(FixtureTemplate.collection(List.of())));
        }
        // Nothing held, so nothing is equal to anything held and this always builds.
        ElementsMadeApart maker = ElementsMadeApart.of(carrier.element(),
                ElementsApart.meet(fields, ElementsKeptApart.at(position, held, reading)),
                size + 1, reading, Set.of());
        Around filled = maker.around(List.of(), Set.of(), size);
        List<FixtureTemplate> elements = filled.elements();
        return (elements.size() < size ? Proposals.NONE
                : Proposals.of(List.of(FixtureTemplate.collection(elements))))
                .meeting(filled.met());
    }

    /**
     * Elements of one type kept apart at some runs of their fields: the values each run may take,
     * and the elements made of them.
     *
     * <p>Held apart from the containers built of them. Which values a run may take and what an
     * element holding some of them is are questions about the element type and the runs, so a
     * caller building several containers around different values asks them once — read again per
     * container, every value an element is offered paid for the same values and the same records.
     */
    private static final class ElementsMadeApart {

        private final Type element;

        /** Runs of fields taken from an element, empty for the element itself, none of them one
         *  another starts with ({@link ElementsApart}). */
        private final List<List<String>> at;

        /** The values each run may take, in the order they are reached and with where their
         *  building was stopped, or null where a run is no run of fields of a record this writes. */
        private final List<Proposals> values;

        /** Each element made, by the texts of the values placed at its runs in their order, with
         *  what making it met; nothing where none could be. */
        private final Map<List<String>, Proposals> made = new HashMap<>();

        private final RuleReadingContext reading;

        private ElementsMadeApart(Type element, List<List<String>> at, List<Proposals> values,
                                  RuleReadingContext reading) {
            this.element = element;
            this.at = at;
            this.values = values;
            this.reading = reading;
        }

        /** Up to {@code many} values at each run of {@code at}. */
        static ElementsMadeApart of(Type element, List<List<String>> at, int many,
                                    RuleReadingContext reading, Set<TypeSymbol> expanding) {
            List<Proposals> values = new ArrayList<>();
            for (List<String> run : at) {
                Type type = typeAt(element, run, reading);
                if (type == null) {
                    return new ElementsMadeApart(element, at, null, reading);
                }
                values.add(distinctValuesOf(type, many, reading, expanding));
            }
            return new ElementsMadeApart(element, at, values, reading);
        }

        /**
         * Every one of {@code held}, and others beside them up to {@code needed} in all, no two of
         * them equal at any run and none written as any of {@code keptOut} — fewer where the values
         * at a run give out, and none where two of {@code held} are equal at one.
         *
         * <p>What {@code held} are at each run is read off them, so the others are kept apart from
         * the values they actually hold and not from what they were asked to. A held value whose
         * run this cannot read — one written as a spread over a value the module states — is apart
         * from nothing here, and what comes back is a proposal the decoder answers.
         *
         * <p>With what of this compiler's these elements met: a value a figure kept out from in
         * front of the ones taken at a run, and what making each element met. Of these elements and
         * not of every container this is asked for, since a value past the ones taken is one this
         * container never reached for.
         */
        Around around(List<FixtureTemplate> held, Set<String> keptOut, int needed) {
            List<Set<Hir.Expr>> taken = new ArrayList<>();
            for (List<String> run : at) {
                Set<Hir.Expr> here = new HashSet<>();
                for (FixtureTemplate each : held) {
                    Hir.Expr value = valueAt(each.value(), run);
                    if (value != null && !here.add(value)) {
                        return new Around(null, CompositionShortfall.NONE);
                    }
                }
                taken.add(here);
            }
            List<FixtureTemplate> out = new ArrayList<>(held);
            if (out.size() >= needed || values == null) {
                return new Around(out, CompositionShortfall.NONE);
            }
            List<Proposals> free = new ArrayList<>();
            for (int r = 0; r < at.size(); r++) {
                Set<Hir.Expr> heldHere = taken.get(r);
                free.add(values.get(r).map(each ->
                        heldHere.contains(bare(each.value())) ? null : each));
            }
            List<List<FixtureTemplate>> freeValues = free.stream().map(Proposals::values).toList();
            CompositionShortfall met = CompositionShortfall.NONE;
            // How far into the values at every run the walk reached, which is what of them it met.
            int reached = 0;
            for (int i = 0; out.size() < needed; i++) {
                reached = i + 1;
                Map<List<String>, FixtureTemplate> placed = new LinkedHashMap<>();
                List<String> written = new ArrayList<>();
                boolean gaveOut = false;
                for (int r = 0; r < at.size() && !gaveOut; r++) {
                    if (i >= freeValues.get(r).size()) {
                        gaveOut = true;
                    } else {
                        FixtureTemplate value = freeValues.get(r).get(i);
                        placed.put(at.get(r), value);
                        written.add(value.text());
                    }
                }
                if (gaveOut) {
                    break;
                }
                Proposals one = made.computeIfAbsent(written,
                        _ -> holdingAt(element, placed, reading).firstOf(1));
                met = met.and(one.met());
                if (!one.isEmpty() && !keptOut.contains(one.values().getFirst().text())) {
                    out.add(one.values().getFirst());
                }
            }
            for (Proposals run : free) {
                met = met.and(run.firstOf(reached).met());
            }
            return new Around(out, met);
        }
    }

    /**
     * Elements made apart, or null where what they were to be built around was not apart itself,
     * and what of this compiler's making them met.
     */
    private record Around(List<FixtureTemplate> elements, CompositionShortfall met) {}

    /**
     * Up to {@code many} values of what an element of type {@code element} holds at {@code run},
     * no two alike, in the order a collection reaches for them — or none where the run is no run
     * of fields of a record this writes.
     *
     * <p>The values a list built around one number per element puts at a run that does not hold
     * the number, so that its elements are apart there as its rules ask: the same values, in the
     * same order, that elements made apart without a number are given ({@link ElementsMadeApart}).
     */
    static Proposals valuesApartAt(Type element, List<String> run, int many,
                                   RuleReadingContext reading) {
        Type type = typeAt(element, run, reading);
        return type == null ? Proposals.NONE : distinctValuesOf(type, many, reading, Set.of());
    }

    /**
     * Whether no two of {@code elements} hold one value at any of {@code runs}.
     *
     * <p>A value whose run this cannot read — one written as a spread over a value the module
     * states — is apart from nothing here, and the decoder answers for it.
     */
    static boolean holdApart(List<FixtureTemplate> elements, List<List<String>> runs) {
        for (List<String> run : runs) {
            Set<Hir.Expr> seen = new HashSet<>();
            for (FixtureTemplate each : elements) {
                Hir.Expr value = valueAt(each.value(), run);
                if (value != null && !seen.add(value)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * What {@code value} holds at the end of {@code run}, under no name it wears, or null where it
     * is not written out field by field down to there.
     */
    private static Hir.Expr valueAt(Hir.Expr value, List<String> run) {
        Hir.Expr at = bare(value);
        for (String field : run) {
            if (!(at instanceof Hir.NewData record) || !record.spreads().isEmpty()) {
                return null;
            }
            Hir.Expr found = null;
            for (Hir.FieldInit each : record.inits()) {
                if (each.name().equals(field)) {
                    found = each.value();
                }
            }
            if (found == null) {
                return null;
            }
            at = bare(found);
        }
        return at;
    }

    /** {@code value} with the names a fixture writes around it taken off, so that two values are
     *  compared as what they wrap. */
    private static Hir.Expr bare(Hir.Expr value) {
        Hir.Expr at = value;
        while (at instanceof Hir.Apply applied && applied.args().size() == 1
                && applied.application() instanceof ApplicationOrigin.ComposedFixture) {
            at = applied.args().getFirst();
        }
        return at;
    }

    /** The type at the end of {@code fields} taken from a value of {@code type}, or null where one
     *  of them is no field of a record. */
    private static Type typeAt(Type type, List<String> fields, RuleReadingContext reading) {
        RuleReadingSource source = reading.source();
        Type at = type;
        for (String field : fields) {
            if (!(TypeView.shapeOf(at, source.inners(), source.symbols(), source.kinds(),
                    source.sums()) instanceof Shape.Product record)) {
                return null;
            }
            at = record.fields().get(field);
            if (at == null) {
                return null;
            }
        }
        return at;
    }

    /**
     * A value of {@code type} holding each of {@code placed} at the run of fields it is placed at,
     * and whatever the rules admit everywhere else — or nothing where one of them cannot be, with
     * what composing the rest met.
     */
    private static Proposals holdingAt(Type type, Map<List<String>, FixtureTemplate> placed,
                                       RuleReadingContext reading) {
        if (placed.containsKey(List.of())) {
            // The value itself, which two runs cannot both be.
            return placed.size() == 1 ? Proposals.of(List.of(placed.get(List.of())))
                    : Proposals.NONE;
        }
        // Read whole, since the record composed is written under every name the position wears.
        RuleReadingSource source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        if (!(view.shape() instanceof Shape.Product record)
                || !(record.name() instanceof TypeSymbol.AtModule named)) {
            return Proposals.NONE;
        }
        Map<String, Map<List<String>, FixtureTemplate>> byField = new LinkedHashMap<>();
        placed.forEach((at, value) -> byField.computeIfAbsent(at.getFirst(),
                _ -> new LinkedHashMap<>()).put(at.subList(1, at.size()), value));
        Map<String, FixtureTemplate> given = new LinkedHashMap<>();
        CompositionShortfall met = CompositionShortfall.NONE;
        for (Map.Entry<String, Map<List<String>, FixtureTemplate>> each : byField.entrySet()) {
            Type field = record.fields().get(each.getKey());
            if (field == null) {
                return Proposals.NONE.meeting(met);
            }
            Proposals inner = holdingAt(field, each.getValue(), reading);
            met = met.and(inner.met());
            if (inner.isEmpty()) {
                return Proposals.NONE.meeting(met);
            }
            given.put(each.getKey(), inner.values().getFirst());
        }
        Proposals composed = Partitions.composed(named,
                Partitions.rulesOver(view.wrappers(), named, source), reading, Set.of(), given);
        met = met.and(composed.met());
        FixtureTemplate written = composed.isEmpty() ? null
                : WornNames.under(view.wrappers(), composed.values().getFirst(), source);
        return Proposals.ofNullable(written).meeting(met);
    }

    /** A map of that many entries, no two of which share a key. The values under the keys are free
     *  to repeat. */
    private static Built ofMapping(Shape.Mapping map, int least, RuleReadingContext reading,
                                   Set<TypeSymbol> expanding) {
        Proposals keyProposals = proposalsFor(map.key(), reading, expanding);
        Proposals valueProposals = proposalsFor(map.value(), reading, expanding);
        List<FixtureTemplate> keys = keyProposals.values();
        List<FixtureTemplate> values = valueProposals.values();
        List<Step> out = new ArrayList<>();
        // Where each side's proposals were stopped, met where the walk first comes to a pair
        // holding the proposal they stand in front of, which is the pair a proposal a figure kept
        // out would have stood in.
        Reaching keysStopped = new Reaching(keyProposals);
        Reaching valuesStopped = new Reaching(valueProposals);
        if (keys.isEmpty() || values.isEmpty()) {
            // Nothing to pair, so every proposal either side would have had is one no map is
            // built of.
            CompositionShortfall met = keyProposals.met().and(valueProposals.met());
            if (!met.nothing()) {
                out.add(new Halted(met));
            }
            return new Built(out);
        }
        int pairs = 0;
        // Every pair, nearest first. A key's rules and a value's are answered together or not at all —
        // the pair is inside one position, so no search outside can put a key's second proposal beside
        // a value's first — and taking them in step would offer only the pairs whose two proposals
        // happen to have been read in the same order. Nearest first is what makes the bound below cost
        // the least: what it drops is the pairs furthest from what either side proposed first.
        // Recorded where the budget is reached and not worked out afterwards from how many were
        // built. How many pairs there are and how many were made differ whenever this stops, and
        // they are the same two numbers whether or not it was this that stopped it — so a reader
        // asking which budget ran out would be reading it off a subtraction that does not know.
        boolean stopped = false;
        // What a key proposal's other keys are, worked out once however many values it is put
        // beside. The question is the key's and the count's — what stands under them is not in it —
        // so a reading per pair is one walk over the element's values run again for every value the
        // other side proposed.
        List<Proposals> keysFrom = new ArrayList<>(Collections.nCopies(keys.size(), null));
        // And the key type's values the others are taken from, which are no key proposal's.
        Proposals keyValues = distinctValuesOf(map.key(), least + 1, reading, expanding);
        pairing:
        for (int apart = 0; apart <= keys.size() + values.size() - 2; apart++) {
            for (int i = Math.max(0, apart - values.size() + 1);
                    i <= Math.min(apart, keys.size() - 1); i++) {
                if (pairs == MOST_PAIRINGS) {
                    stopped = true;
                    break pairing;
                }
                if (keysFrom.get(i) == null) {
                    keysFrom.set(i, distinctFrom(keys.get(i), keyValues, least));
                }
                halt(out, keysStopped.through(new int[] {i})
                        .and(valuesStopped.through(new int[] {apart - i})));
                FixtureTemplate value = values.get(apart - i);
                List<FixtureTemplate> entries = new ArrayList<>();
                for (FixtureTemplate key : keysFrom.get(i).values()) {
                    entries.add(FixtureTemplate.entry(key, value));
                }
                // What the keys beside this one met in front of the ones it took.
                if (!keysFrom.get(i).met().nothing()) {
                    out.add(new Halted(keysFrom.get(i).met()));
                }
                out.add(new Made(FixtureTemplate.collection(entries), entries.size()));
                pairs++;
            }
        }
        if (stopped) {
            out.add(new Halted(CompositionShortfall.of(
                    List.of(CompositionBudget.PAIRINGS_BUILT_AT_ONCE))));
        } else {
            // Every pair walked, so a proposal stopped past the last of either side is one the walk
            // would have gone on to.
            halt(out, keysStopped.rest().and(valuesStopped.rest()));
        }
        return new Built(out);
    }

    /** A step stopped by {@code met}, where it met something. */
    private static void halt(List<Step> out, CompositionShortfall met) {
        if (!met.nothing()) {
            out.add(new Halted(met));
        }
    }

    /**
     * What stopped {@code proposals} in front of each of its values, by the value's place, and
     * last what stopped it past the last of them.
     */
    private static List<CompositionShortfall> stopsBefore(Proposals proposals) {
        List<CompositionShortfall> out = new ArrayList<>();
        CompositionShortfall here = CompositionShortfall.NONE;
        for (Proposals.Entry entry : proposals.entries()) {
            switch (entry) {
                case Proposals.Stopped(CompositionShortfall met) -> here = here.and(met);
                case Proposals.Offered _ -> {
                    out.add(here);
                    here = CompositionShortfall.NONE;
                }
            }
        }
        out.add(here);
        return out;
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
    private static Proposals proposalsFor(Type type, RuleReadingContext reading,
                                          Set<TypeSymbol> expanding) {
        return Partitions.representativesOf(type, reading, null, expanding);
    }

    /**
     * A collection of {@code carrier} holding every one of {@code holding}, nothing equal to any of
     * {@code keptOut}, and as many as the rules let it hold — or nothing where none can be built,
     * with what of this compiler's the build met.
     *
     * <p>For a row being built around what it is asked to hold. What the rest are is not what was
     * asked for, and what they may be is: a list may hold the same value again and a set may not,
     * nor a list whose rules keep its elements apart ({@code apart}, as {@link ElementsApart} reads
     * them), and a caller padding one by hand would have to know which — the thing this reader is
     * for.
     *
     * <p><b>What it is to hold is values, and not elements.</b> Holding a value asks which values
     * are in it, so two values handed over that are one value are one element whichever carrier it
     * is — a list asked to hold {@code a} twice holds it once, and is not refused for room it does
     * not need. What a list may say again is what fills it to the rules' floor beside them.
     *
     * <p><b>How many is worked out here, where the values are in hand.</b> The fewest the rules
     * allow, and never fewer than the values it holds. A container holding nothing asked of it and
     * kept to the rules' floor may hold none at all.
     *
     * <p>Nothing where the values cannot all stand together: one value both written in and kept
     * out, more than the rules leave room for, or a type with too few values to fill the rest with
     * none kept out. Each of those is a container nothing can build, said as nothing built rather
     * than as a container of the wrong size or holding what it was to hold none of. And nothing,
     * having met a figure, where it is this compiler that would not build it: more than a proposal
     * holds, or too few values because the element's were cut short.
     */
    static Proposals holding(Shape.Sequence carrier, List<List<String>> apart,
                             List<FixtureTemplate> holding, List<FixtureTemplate> keptOut,
                             DeclaredBounds.CountRange holds, RuleReadingContext reading) {
        Elements elements = elementsHolding(carrier.element(), apart, holding, keptOut, holds,
                reading);
        return (elements.held() == null ? Proposals.NONE
                : Proposals.of(List.of(FixtureTemplate.collection(elements.held()))))
                .meeting(elements.met());
    }

    /**
     * The same, of a map: values that hold every one of {@code holding} and nothing equal to any of
     * {@code keptOut}, each under a key of its own.
     *
     * <p>What is asked of a map's element is asked of its values, which may repeat the way a list's
     * elements may. The keys are what keeps the entries apart, and they are the key type's distinct
     * values, the same ones a map built to a size is keyed by ({@link #ofMapping}).
     *
     * <p>{@code filed}, where there is one, is a key a class was put at and the value of
     * {@code holding} it is filed under — the entry holding the element is the entry the key is
     * about. Every other entry is keyed apart from it, since a map holds one entry under a key.
     *
     * <p>{@code eachFiled} are keys each asked of an entry of its own, over whatever value the
     * rules admit. A key among them that is {@code filed}'s, or another of them, is one entry.
     */
    static Proposals holding(Shape.Mapping map,
                             List<FixtureTemplate> holding, List<FixtureTemplate> keptOut,
                             Filed filed, List<FixtureTemplate> eachFiled,
                             List<FixtureTemplate> keysKeptOut,
                             DeclaredBounds.CountRange holds,
                             RuleReadingContext reading) {
        Set<String> out = new LinkedHashSet<>();
        keysKeptOut.forEach(each -> out.add(each.text()));
        if (filed != null && out.contains(filed.key().text())) {
            return Proposals.NONE;
        }
        Set<String> filedKeys = new LinkedHashSet<>();
        if (filed != null) {
            filedKeys.add(filed.key().text());
        }
        List<FixtureTemplate> apart = new ArrayList<>();
        for (FixtureTemplate each : eachFiled) {
            if (out.contains(each.text())) {
                return Proposals.NONE;
            }
            if (filedKeys.add(each.text())) {
                apart.add(each);
            }
        }
        // A key chosen over no value in particular needs an entry to be the key of, so the map holds
        // at least one value for each such key whatever else is asked of it.
        int keyed = filedKeys.size();
        DeclaredBounds.CountRange room = keyed > 0
                ? new DeclaredBounds.CountRange(Math.max(keyed, holds.least()), holds.most())
                : holds;
        Elements filled = elementsHolding(map.value(), List.of(), holding, keptOut, room, reading);
        CompositionShortfall met = filled.met();
        List<FixtureTemplate> values = filled.held();
        if (values == null) {
            return Proposals.NONE.meeting(met);
        }
        // Where the value the key is chosen for stands among them, asked of the values rather than
        // assumed from the order they were handed in. Any of them, where none was chosen.
        int under = -1;
        if (filed != null) {
            for (int i = 0; i < values.size() && under < 0; i++) {
                if (filed.value() == null || values.get(i).text().equals(filed.value().text())) {
                    under = i;
                }
            }
            if (under < 0) {
                throw new IllegalStateException(filed.value() == null
                        ? "a key was chosen and the map was built holding no value to file it over"
                        : "a key was chosen for a value the map is not built to hold: "
                                + filed.value().text());
            }
        }
        // A key no entry may have is one no other entry is filed under either.
        Set<String> written = new LinkedHashSet<>(filedKeys);
        written.addAll(out);
        // One more than is needed for each key already chosen, so that those being among them
        // still leaves enough beside them, and as many more as are kept out.
        List<FixtureTemplate> others = new ArrayList<>();
        int needed = values.size() - keyed;
        Proposals keys = distinctValuesOf(map.key(), values.size() + keyed + keysKeptOut.size(),
                reading, Set.of());
        // What the keys met in front of the ones taken, and all of it where they ran out.
        for (Proposals.Entry each : keys.entries()) {
            if (others.size() == needed) {
                break;
            }
            switch (each) {
                case Proposals.Stopped(CompositionShortfall stop) -> met = met.and(stop);
                case Proposals.Offered(FixtureTemplate key) -> {
                    if (written.add(key.text())) {
                        others.add(key);
                    }
                }
            }
        }
        if (others.size() < needed) {
            return Proposals.NONE.meeting(met);
        }
        List<FixtureTemplate> entries = new ArrayList<>();
        int nextApart = 0;
        int next = 0;
        for (int i = 0; i < values.size(); i++) {
            FixtureTemplate key = i == under ? filed.key()
                    : nextApart < apart.size() ? apart.get(nextApart++) : others.get(next++);
            entries.add(FixtureTemplate.entry(key, values.get(i)));
        }
        return Proposals.of(List.of(FixtureTemplate.collection(entries))).meeting(met);
    }

    /**
     * A key chosen for a map, and the value it is to be filed under.
     *
     * @param key   the key, which a class was put at
     * @param value the value under it, which is one of the values the map is built to hold — or
     *              null where nothing was asked of the value, and any value the rules admit will do
     */
    record Filed(FixtureTemplate key, FixtureTemplate value) {

        Filed {
            Objects.requireNonNull(key, "a key is filed");
        }
    }

    /**
     * What a container holds, or null where nothing can be built, and what of this compiler's
     * the filling of it met.
     *
     * @param held the elements, which may be none — an empty container is one that was built
     */
    private record Elements(List<FixtureTemplate> held, CompositionShortfall met) {

        static final Elements NONE = new Elements(null, CompositionShortfall.NONE);
    }

    /**
     * What a container of {@code element} holds when it holds every one of {@code holding},
     * nothing equal to any of {@code keptOut}, and as many as the rules let it — or nothing where
     * nothing can.
     *
     * <p>Two ways of nothing, told apart by what comes with it. More than the rules leave room for
     * is the model's answer and meets nothing; more than a proposal holds is this compiler's, and
     * meets the figure — a reader told the first goes looking at the rules, and one told the second
     * at the figure, so the two cannot be one null.
     *
     * @param apart what the values are to be apart at, as {@link ElementsApart} reads it: nothing
     *              where they may repeat, which a list's elements and a map's values may unless a
     *              rule says otherwise
     */
    private static Elements elementsHolding(Type element, List<List<String>> apart,
                                            List<FixtureTemplate> holding,
                                            List<FixtureTemplate> keptOut,
                                            DeclaredBounds.CountRange holds,
                                            RuleReadingContext reading) {
        Set<String> out = new LinkedHashSet<>();
        keptOut.forEach(each -> out.add(each.text()));
        Set<String> written = new LinkedHashSet<>();
        List<FixtureTemplate> elements = new ArrayList<>();
        for (FixtureTemplate each : holding) {
            if (out.contains(each.text())) {
                return Elements.NONE;
            }
            if (written.add(each.text())) {
                elements.add(each);
            }
        }
        int needed = Math.max(holds.least(), elements.size());
        if (needed > holds.most()) {
            return Elements.NONE;
        }
        CompositionBudget past = pastTheElements(needed);
        if (past != null) {
            return new Elements(null, CompositionShortfall.of(List.of(past)));
        }
        // Fewer than asked for is a type with too few values, which is a container the rules want
        // and nothing can build — or values cut at a figure, which what they met says.
        if (!apart.isEmpty()) {
            // One more than the values that may be passed over, since each kept out or already
            // held may be among them.
            ElementsMadeApart maker = ElementsMadeApart.of(element, apart,
                    needed + out.size() + elements.size() + 1, reading, Set.of());
            Around around = maker.around(elements, out, needed);
            return new Elements(around.elements() == null || around.elements().size() < needed
                    ? null : around.elements(), around.met());
        }
        // A container that may say one of its values again says the one it was asked to hold,
        // which is the value that is surely one the element's rules admit.
        if (!elements.isEmpty()) {
            while (elements.size() < needed) {
                elements.add(elements.getFirst());
            }
            return new Elements(elements, CompositionShortfall.NONE);
        }
        // The first value not kept out, with what was met in front of it — all of it, where every
        // value is kept out.
        CompositionShortfall met = CompositionShortfall.NONE;
        for (Proposals.Entry entry : distinctValuesOf(element, needed + out.size() + 1, reading,
                Set.of()).entries()) {
            switch (entry) {
                case Proposals.Stopped(CompositionShortfall stop) -> met = met.and(stop);
                case Proposals.Offered(FixtureTemplate each) -> {
                    if (!out.contains(each.text())) {
                        while (elements.size() < needed) {
                            elements.add(each);
                        }
                        return new Elements(elements, met);
                    }
                }
            }
        }
        return new Elements(needed == 0 ? elements : null, met);
    }

    /**
     * {@code seed} and up to {@code least} values in all, no two of them equal, the others taken
     * from {@code values} — the type's distinct values, one more than {@code least} since the seed
     * is likely to be among them, read once by a caller with several seeds.
     *
     * <p>Fewer than asked where the type runs out, which is not the same as failing: a set of three
     * booleans is a thing no value satisfies, and offering the two that exist is a proposal the decoder
     * answers the way it answers any other.
     *
     * <p>With the stops in front of the values taken, and every stop where the values ran out.
     */
    private static Proposals distinctFrom(FixtureTemplate seed, Proposals values, int least) {
        Proposals.Gathering out = Proposals.Gathering.distinct();
        out.add(seed);
        out.addAll(values, least);
        return out.done();
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
     * is built from both of them or from nothing. Then the values the rules about the strings admit,
     * which are values of the type in the same way and are as many as the rules leave. Then values
     * made by stepping the carrier, which stay inside the rules the type carries. The type's own
     * proposals come last: each is what one rule asked for and any of them may be one the whole of
     * the rules refuses, so a collection filled from them is refused for its elements — which is
     * still better than a collection short of its size, and is all there is where the carrier
     * neither divides nor steps.
     *
     * <p><b>Which is why the rules about the strings are asked before the carrier is stepped.</b> A
     * string stepped by a character is a value of the carrier and not of the type: what the carrier
     * answers is how many characters, and a type whose rule says which of them gets a string it
     * refuses at every element after the first. The rules are what tell the values apart there, the
     * same as a range does for a number ({@link Partitions#numberInside}).
     *
     * <p>Then, for a type with no carrier to step, values that differ in what they hold: a record at
     * one of its fields and a collection in how many it holds ({@link #differing}). A list kept
     * apart as records, or as lists, has its elements from here — taken from the proposals alone it
     * had one of them, and a list of two was a list saying one value twice.
     *
     * <p>With what of this compiler's each step that ran met. Fewer than {@code many} is a type
     * with no more values or a build cut at a figure, and only what was met tells the two apart —
     * a set of two of a value no proposal holds is not a set the type has too few values for.
     */
    static Proposals distinctValuesOf(Type type, int many, RuleReadingContext reading,
                                      Set<TypeSymbol> expanding) {
        return distinctValuesOf(type, many, null, AdmissibleSet.complete(ValueSet.ANY), reading,
                expanding);
    }

    /**
     * The same, of a value at a field whose record's rules say what it holds ({@code held}, null
     * where nothing holds it) and which values may stand there ({@code atThePlace}): a collection
     * differing in how many it holds holds as many as those rules leave, kept apart as they keep
     * it, and the values offered first are the ones the field is read as dividing into
     * ({@link #placed}), and the only ones where they are every value it can hold.
     */
    static Proposals distinctValuesOf(Type type, int many, FieldDomains.Held held,
                                      AdmissibleSet atThePlace,
                                      RuleReadingContext reading,
                                      Set<TypeSymbol> expanding) {
        // Each step's values and stops taken in its order until there are as many as asked for, so
        // a stop is kept where the walk came to it and one past the last value taken is never
        // reached.
        Proposals.Gathering out = Proposals.Gathering.distinct();
        Placed placed = placed(type, atThePlace, reading, expanding);
        out.addAll(placed.offered(), many);
        if (placed.everyValue() || out.size() >= many) {
            return out.done();
        }
        for (FixtureTemplate each : Partitions.admittedStrings(type, reading, many)) {
            if (out.size() >= many) {
                return out.done();
            }
            out.add(each);
        }
        for (int i = 0; out.size() < many; i++) {
            Proposals each = varied(type, i, reading);
            out.addAll(each, many);
            if (each.isEmpty()) {
                break;
            }
        }
        if (out.size() >= many) {
            return out.done();
        }
        out.addAll(reading.revision().settled(new Differing(type, many, held, reading, expanding)),
                many);
        if (out.size() >= many) {
            return out.done();
        }
        // Asked last and only where there is room for what it answers. What a position is offered
        // is a reading of every rule on it and costs what that reading costs, and a loop that asks
        // for the list and then leaves it alone pays for it at every count already filled.
        out.addAll(Partitions.representativesOf(type, reading, null, expanding), many);
        return out.done();
    }

    /**
     * The values {@link #differing} builds, as work settled by everything they are built from: the
     * type, how many, what holds it, the names it is inside, and the source and policy the rules
     * are read under — the source by its origin, as {@link Partitions.ARecordComposed} is keyed.
     *
     * <p>Kept, because each is a record or a collection composed under its rules, and a list kept
     * apart asks for them at every size and every point a search visits. Kept whole, with what the
     * build met: a reader handed the values from here and the figure from a second build would
     * hold two answers that agree only while the two builds do.
     */
    private static final class Differing implements RevisionWork<Proposals> {

        private final Type type;

        private final int many;

        private final FieldDomains.Held held;

        private final Set<TypeSymbol> expanding;

        private final RuleReadingSource.Origin origin;

        private final ReadingPolicy policy;

        private final RuleReadingContext reading;

        Differing(Type type, int many, FieldDomains.Held held, RuleReadingContext reading,
                  Set<TypeSymbol> expanding) {
            this.type = type;
            this.many = many;
            this.held = held;
            this.expanding = Set.copyOf(expanding);
            this.origin = reading.source().origin();
            this.policy = reading.policy();
            this.reading = reading;
        }

        @Override
        public Proposals workedOut(RevisionKnowledge revision) {
            return differing(type, many, held, reading, expanding);
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Differing it && type.equals(it.type) && many == it.many
                    && Objects.equals(held, it.held) && expanding.equals(it.expanding)
                    && origin.equals(it.origin) && policy.equals(it.policy);
        }

        @Override
        public int hashCode() {
            return Objects.hash(type, many, held, expanding, origin, policy);
        }

        @Override
        public String toString() {
            return "Differing[" + many + " of " + type + " inside " + expanding + "]";
        }
    }

    /**
     * Values of {@code type} that differ in what they hold, up to {@code many} of them, under every
     * name it wears: a record's at its fields ({@link Partitions#differingAtItsFields}) and a
     * collection's in how many it holds, from the fewest its rules and {@code held} leave. Nothing
     * for a type that holds nothing of its own, whose values were asked for above.
     *
     * <p>Each built as a value of its position is, under the rules there, so what differs is a
     * value of the type and not a shape that carries a difference.
     *
     * <p>And what a value of the type may be beyond the one each of its kinds stands for: an
     * optional's every value of what it holds, a sum's every value of each of its cases, and a
     * collection's every content at every size ({@link #arrange}). A set of such values is built
     * from as many of them as it holds, and the one per kind the type divides into ran out at the
     * number of kinds. Each is walked in one order and stopped at {@code many}, so what comes back
     * is as many values as the type has up to that number. The contents of a collection beyond
     * the one built at each size are proposals and not built values — a rule over what it holds
     * is the decoder's to apply — so they come after every size was built once.
     */
    private static Proposals differing(Type type, int many, FieldDomains.Held held,
                                       RuleReadingContext reading, Set<TypeSymbol> expanding) {
        RuleReadingSource source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        Set<TypeSymbol> inside = new LinkedHashSet<>(expanding);
        for (TypeSymbol wears : view.wrappers()) {
            if (!inside.add(wears)) {
                return Proposals.NONE;
            }
        }
        return switch (view.shape()) {
            case Shape.Product record -> {
                if (!(record.name() instanceof TypeSymbol.AtModule named)) {
                    yield Proposals.NONE;
                }
                yield worn(view, Partitions.differingAtItsFields(named,
                        Partitions.rulesOver(view.wrappers(), named, source), many, reading,
                        inside), source);
            }
            case Shape.Sequence _, Shape.Mapping _ -> {
                DeclaredBounds.CountRange range = Partitions.heldRange(type, reading, held);
                List<List<String>> apart = ElementsKeptApart.heldBy(held);
                Proposals.Gathering out = Proposals.Gathering.distinct();
                // Up to the first size that builds nothing: one holding more is built of what
                // that one could not have, so the sizes past it are walked for nothing — and
                // where the rules cap no size, walked as far as a count goes.
                for (int size = Math.max(range.least(), 0);
                     size <= range.most() && out.size() < many; size++) {
                    // The first value at the size, which is all of it this takes, with what was
                    // met in front of it — and where there is none, what stopped it.
                    // Built as the collection the names are worn over, so the names are put on
                    // here as they are on every value this answers.
                    Proposals one = ofSize(view, size, apart, reading, inside).firstOf(1);
                    out.addAll(worn(view, one, source), many);
                    if (one.isEmpty()) {
                        break;
                    }
                }
                // Then every other content, where the elements are apart as wholes or not at all.
                // One kept apart at a field of its elements holds a few its rules choose, and an
                // arrangement of the element's values would offer some that share the field.
                // Read with the rules of the names the collection wears, as the value built at
                // each size reads them: a list a newtype keeps apart is apart here too.
                List<List<String>> keptApart = view.shape() instanceof Shape.Sequence
                        ? ElementsKeptApart.at(view, apart, reading) : apart;
                if (out.size() < many && keptApart.stream().allMatch(List::isEmpty)) {
                    arrange(view.shape(), !keptApart.isEmpty(), range, many, reading, inside,
                            out, content -> WornNames.under(view.wrappers(), content, source));
                }
                yield out.done();
            }
            // Nothing, and every value of what it holds. What it holds is written as itself.
            case Shape.Optional optional -> {
                Proposals.Gathering values = Proposals.Gathering.inOrder();
                values.add(FixtureTemplate.none());
                values.addAll(distinctValuesOf(optional.element(), many - 1, reading, inside));
                yield worn(view, values.done(), source);
            }
            // A value of a sum is a value of one of its cases, written as that case is.
            case Shape.Sum sum -> worn(view, ofEachCase(sum.reaches().cases(), sum.name(), many,
                    reading, inside), source);
            // In an order of their own, since a union's members are a set and come in none.
            case Shape.Cases cases -> worn(view, ofEachCase(cases.members().stream()
                            .sorted(Comparator.comparing(TypeSymbol::toString)).toList(),
                    null, many, reading, inside), source);
            case Shape.Scalar _, Shape.Unit _, Shape.Unresolved _, Shape.Tuple _,
                 Shape.Function _, Shape.Uninhabited _, Shape.Bottom _, Shape.Erroneous _,
                 Shape.Undecided _ -> Proposals.NONE;
        };
    }

    /**
     * {@code values} under the names {@code view} wears, leaving out any those names cannot be
     * written on here ({@link WornNames#under}), the stops where they stood.
     */
    private static Proposals worn(TypeView view, Proposals values, RuleReadingSource source) {
        return values.map(each -> WornNames.under(view.wrappers(), each, source));
    }

    /**
     * Up to {@code many} values of the cases of a sum, taking each case's values in turn and one
     * from each before a second from any, so that a few of them are not all of one case.
     *
     * <p>Each case is asked for its share of {@code many} and no more, and the share is doubled
     * for the cases that filled it only while the values together fall short. Asked for
     * {@code many} each, a sum of many cases built that many of every case to keep a few.
     *
     * @param sum the sum's own name, which a case reached from inside it does not open again; null
     *            for a union, which has none
     */
    private static Proposals ofEachCase(List<TypeSymbol> cases, TypeSymbol sum, int many,
                                        RuleReadingContext reading, Set<TypeSymbol> inside) {
        Set<TypeSymbol> within = new LinkedHashSet<>(inside);
        if (sum != null && !within.add(sum)) {
            return Proposals.NONE;
        }
        List<TypeSymbol> open = cases.stream().filter(leaf -> !within.contains(leaf)).toList();
        if (open.isEmpty() || many <= 0) {
            return Proposals.NONE;
        }
        // Each case's values as last read: a case read again at a larger share is the whole answer
        // for it, with where it was stopped.
        List<Proposals> each = new ArrayList<>(Collections.nCopies(open.size(), Proposals.NONE));
        boolean[] spent = new boolean[open.size()];
        int share = Math.max(1, (many + open.size() - 1) / open.size());
        while (true) {
            boolean anyFilled = false;
            for (int i = 0; i < open.size(); i++) {
                if (spent[i]) {
                    continue;
                }
                Proposals values = distinctValuesOf(Type.ref(open.get(i)), share, reading, within);
                each.set(i, values);
                spent[i] = values.values().size() < share;
                anyFilled |= !spent[i];
            }
            Proposals out = takenInTurn(each, many);
            if (out.values().size() >= many || !anyFilled || share >= many) {
                return out;
            }
            share = Math.min(many, share * 2);
        }
    }

    /**
     * Up to {@code many} of {@code each}, the first of every list before the second of any — and
     * each stop where its own list put it, in front of the value it stood before, so a case stopped
     * where it would have given the second value is met where that second value would have been
     * taken.
     */
    private static Proposals takenInTurn(List<Proposals> each, int many) {
        // Each list cut into turns: the stops in front of a value and the value, and last the stops
        // after its last value.
        List<List<List<Proposals.Entry>>> turns = new ArrayList<>();
        for (Proposals values : each) {
            List<List<Proposals.Entry>> cut = new ArrayList<>();
            List<Proposals.Entry> turn = new ArrayList<>();
            for (Proposals.Entry entry : values.entries()) {
                turn.add(entry);
                if (entry instanceof Proposals.Offered) {
                    cut.add(turn);
                    turn = new ArrayList<>();
                }
            }
            cut.add(turn);
            turns.add(cut);
        }
        Proposals.Gathering out = Proposals.Gathering.inOrder();
        for (int i = 0; out.size() < many; i++) {
            boolean more = false;
            for (List<List<Proposals.Entry>> cut : turns) {
                if (i < cut.size() && out.size() < many) {
                    out.addAll(new Proposals(cut.get(i)), many);
                    more = true;
                }
            }
            if (!more) {
                break;
            }
        }
        return out.done();
    }

    /**
     * Every content of a collection of {@code shape} the count range leaves, smallest first,
     * handed to {@code offer} until it answers false: each few of the element's values a set can
     * hold, each run of them a list can, and each few of the keys with each run of values for a
     * map — where a list's elements or a map's values are apart, each order of each few.
     *
     * <p>Arranged from the first {@code many} values of what it holds, which is enough to tell
     * {@code many} contents apart. Proposals and not built values: a rule over what the collection
     * holds is the decoder's to apply.
     *
     * <p>Into {@code out}, each content after what stopped a value of what it holds in front of
     * the furthest value it takes — a content of values the walk would have reached past one a
     * figure kept out is a content taken in place of one holding that value — until {@code out}
     * holds {@code many}. Where the contents run out first, after them every stop the values had
     * left, and a size past what a proposal holds.
     *
     * @param apart   whether the elements are apart as wholes, so that a list or a map's values
     *                say no value twice; a set's never do
     * @param written what a content is written as, or null where it is written as nothing
     */
    private static void arrange(Shape shape, boolean apart, DeclaredBounds.CountRange range,
                                int many, RuleReadingContext reading, Set<TypeSymbol> inside,
                                Proposals.Gathering out,
                                Function<FixtureTemplate, FixtureTemplate> written) {
        int least = Math.max(range.least(), 0);
        // What tells two contents apart is the shape's: a set is the few it holds, and a list or
        // what a map files under its keys is in an order as well.
        Picking runs = apart ? Picking.AN_ORDER_OF_A_FEW : Picking.A_RUN;
        switch (shape) {
            case Shape.Sequence(Shape.Sequence.Kind kind, Type element) -> {
                Reaching elements = new Reaching(distinctValuesOf(element, many, reading, inside));
                List<FixtureTemplate> values = elements.values();
                Picking picking = kind == Shape.Sequence.Kind.SET ? Picking.A_FEW : runs;
                for (int size = least; size <= range.most(); size++) {
                    if (!picking.fits(size, values.size())) {
                        out.stop(elements.rest());
                        return;
                    }
                    CompositionBudget past = pastTheElements(size);
                    if (past != null) {
                        out.stop(elements.rest().and(CompositionShortfall.of(List.of(past))));
                        return;
                    }
                    int[] at = picking.first(size);
                    do {
                        out.stop(elements.through(at));
                        FixtureTemplate each =
                                written.apply(FixtureTemplate.collection(picked(values, at)));
                        if (each != null) {
                            out.add(each);
                        }
                        if (out.size() >= many) {
                            return;
                        }
                    } while (picking.next(at, values.size()));
                }
                out.stop(elements.rest());
            }
            case Shape.Mapping(Type key, Type value) -> {
                Reaching keyValues = new Reaching(distinctValuesOf(key, many, reading, inside));
                Reaching valueValues = new Reaching(distinctValuesOf(value, many, reading,
                        inside));
                List<FixtureTemplate> keys = keyValues.values();
                List<FixtureTemplate> values = valueValues.values();
                for (int size = least; size <= range.most(); size++) {
                    if (!Picking.A_FEW.fits(size, keys.size())
                            || !runs.fits(size, values.size())) {
                        out.stop(keyValues.rest().and(valueValues.rest()));
                        return;
                    }
                    CompositionBudget past = pastTheElements(size);
                    if (past != null) {
                        out.stop(keyValues.rest().and(valueValues.rest())
                                .and(CompositionShortfall.of(List.of(past))));
                        return;
                    }
                    int[] which = Picking.A_FEW.first(size);
                    do {
                        List<FixtureTemplate> held = picked(keys, which);
                        int[] to = runs.first(size);
                        do {
                            List<FixtureTemplate> entries = new ArrayList<>();
                            for (int i = 0; i < size; i++) {
                                entries.add(FixtureTemplate.entry(held.get(i),
                                        values.get(to[i])));
                            }
                            out.stop(keyValues.through(which).and(valueValues.through(to)));
                            FixtureTemplate each =
                                    written.apply(FixtureTemplate.collection(entries));
                            if (each != null) {
                                out.add(each);
                            }
                            if (out.size() >= many) {
                                return;
                            }
                        } while (runs.next(to, values.size()));
                    } while (Picking.A_FEW.next(which, keys.size()));
                }
                out.stop(keyValues.rest().and(valueValues.rest()));
            }
            case Shape.Scalar _, Shape.Product _, Shape.Sum _, Shape.Unit _, Shape.Optional _,
                 Shape.Unresolved _, Shape.Cases _, Shape.Tuple _, Shape.Function _,
                 Shape.Uninhabited _, Shape.Bottom _, Shape.Erroneous _, Shape.Undecided _ -> { }
        }
    }

    /**
     * Values arranged into contents, and how far into them the arranging has reached: what
     * stopped a value in front of the furthest one taken so far is met once, as the arranging
     * first reaches past it.
     */
    private static final class Reaching {

        private final List<FixtureTemplate> values;

        /** What stopped the values in front of each of them by its place, and last past them. */
        private final List<CompositionShortfall> before;

        /** How many places' stops have been met. */
        private int reached;

        Reaching(Proposals proposals) {
            this.values = proposals.values();
            this.before = stopsBefore(proposals);
        }

        List<FixtureTemplate> values() {
            return values;
        }

        /** What stops in front of the furthest of the places {@code at} names have not been met. */
        CompositionShortfall through(int[] at) {
            int furthest = -1;
            for (int each : at) {
                furthest = Math.max(furthest, each);
            }
            return metUpTo(furthest + 1);
        }

        /** Every stop not yet met, past the last value as well: the arranging went to the end. */
        CompositionShortfall rest() {
            return metUpTo(before.size());
        }

        private CompositionShortfall metUpTo(int places) {
            CompositionShortfall out = CompositionShortfall.NONE;
            for (; reached < places; reached++) {
                out = out.and(before.get(reached));
            }
            return out;
        }
    }

    /** The values {@code at} names, in its order. */
    private static List<FixtureTemplate> picked(List<FixtureTemplate> values, int[] at) {
        List<FixtureTemplate> out = new ArrayList<>(at.length);
        for (int i : at) {
            out.add(values.get(i));
        }
        return out;
    }

    /**
     * Which places of {@code n} values a content of {@code size} names, walked one after another.
     *
     * <p>Two questions and not one: whether a value may be named twice, and whether the order
     * they are named in tells two contents apart. A set answers no to both, a list free to repeat
     * yes to both, and a list or a map's values kept apart no and yes — so each order of each few.
     * Answered as one, a list kept apart would be walked as a set is, and of three values held
     * three apart would offer one list where there are six.
     *
     * <p>Each step is as long as the content and passes nothing over, so a walk stopped at a
     * number of contents costs that number of steps.
     */
    private enum Picking {

        /** Each few, in the order the values come: a set's contents. */
        A_FEW,

        /** Each order of each few: a list's, or a map's values, kept apart. */
        AN_ORDER_OF_A_FEW,

        /** Each run, a value as often as it comes, counting as a number does: a list's. */
        A_RUN;

        /** Whether {@code size} places can be named among {@code n} values this way. */
        boolean fits(int size, int n) {
            return size == 0 || (n > 0 && (this == A_RUN || size <= n));
        }

        /** The first of {@code size} places: nought upwards where no value is named twice, and
         *  nought everywhere where one may be. */
        int[] first(int size) {
            int[] at = new int[size];
            for (int i = 0; this != A_RUN && i < size; i++) {
                at[i] = i;
            }
            return at;
        }

        /** {@code at} moved on to the next of its kind among {@code n} values, or false where it
         *  was the last. */
        boolean next(int[] at, int n) {
            return switch (this) {
                case A_FEW -> nextFew(at, n);
                // The next order of the same few, and past the last of them — which is the few
                // the other way round — the first order of the next few.
                case AN_ORDER_OF_A_FEW -> {
                    if (nextOrder(at)) {
                        yield true;
                    }
                    reverse(at);
                    yield nextFew(at, n);
                }
                case A_RUN -> nextRun(at, n);
            };
        }

        /** {@code at}, a few in the order the values come, moved on to the next few. */
        private static boolean nextFew(int[] at, int n) {
            for (int i = at.length - 1; i >= 0; i--) {
                if (at[i] < n - at.length + i) {
                    at[i]++;
                    for (int j = i + 1; j < at.length; j++) {
                        at[j] = at[j - 1] + 1;
                    }
                    return true;
                }
            }
            return false;
        }

        /** {@code at} moved on to the next order of the values it names, or false where it was
         *  the last of them, which leaves them the other way round from the first. */
        private static boolean nextOrder(int[] at) {
            int i = at.length - 2;
            while (i >= 0 && at[i] > at[i + 1]) {
                i--;
            }
            if (i < 0) {
                return false;
            }
            int j = at.length - 1;
            while (at[j] < at[i]) {
                j--;
            }
            swap(at, i, j);
            for (int left = i + 1, right = at.length - 1; left < right; left++, right--) {
                swap(at, left, right);
            }
            return true;
        }

        /** {@code at} the other way round. */
        private static void reverse(int[] at) {
            for (int left = 0, right = at.length - 1; left < right; left++, right--) {
                swap(at, left, right);
            }
        }

        private static void swap(int[] at, int i, int j) {
            int held = at[i];
            at[i] = at[j];
            at[j] = held;
        }

        /** {@code at} moved on to the next run of {@code n} values. */
        private static boolean nextRun(int[] at, int n) {
            int i = at.length - 1;
            while (i >= 0 && at[i] == n - 1) {
                at[i] = 0;
                i--;
            }
            if (i < 0) {
                return false;
            }
            at[i]++;
            return true;
        }
    }

    /**
     * What stands at a place whose own rules admit {@code atThePlace}: a value for each class the
     * place divides into, under every name its type wears — a {@code Bool} is two of them, a sum
     * its cases, a type whose rules name a few values those values — and whether those are every
     * value the place can hold.
     *
     * <p>The one answer every builder of a value at a place starts from, so that what is offered
     * at a place is what the place is read as dividing into ({@link PartitionClasses#casesAt}). Asked
     * by each builder for itself, a builder offers a case the place's rules leave nothing in and
     * takes the whole value it is building with it.
     *
     * <p><b>Every value where the rules name finitely many.</b> A finite set the rules leave is an
     * upper bound however much of them was read ({@link AdmissibleSet}), so a value outside it is
     * one the rules refuse — stepped, composed or proposed, it only takes what holds it with it.
     */
    static Placed placed(Type type, AdmissibleSet atThePlace, RuleReadingContext reading,
                         Set<TypeSymbol> expanding) {
        RuleReadingSource source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        Proposals.Gathering out = Proposals.Gathering.inOrder();
        for (PartitionClass each : PartitionClasses.of(
                PartitionClasses.casesAt(view, atThePlace, reading), view, reading, expanding)) {
            out.addAll(Partitions.standingFor(each.representatives(), reading, expanding));
        }
        return new Placed(out.done(), namesFinitelyMany(atThePlace)
                || namesFinitelyMany(PartitionClasses.admittedByItsNames(view, reading)));
    }

    /**
     * What stands at a place, out of the classes it divides into.
     *
     * @param offered    a value for each class, in the order the classes are read, and where a
     *                   class was left with none for a figure, that — so a class with nothing for
     *                   this compiler's reasons is not read as a class with nothing to have
     * @param everyValue whether those are every value the place can hold, so that nothing else
     *                   is to be offered there
     */
    record Placed(Proposals offered, boolean everyValue) {

        /** The values alone. */
        List<FixtureTemplate> values() {
            return offered.values();
        }

        /** These kept to the numbers {@code within} leaves, where a value is a number and a range
         *  is known; a value that is no number is not one a range says anything about. */
        Placed within(NumericDomain.Bounds within) {
            if (within == null) {
                return this;
            }
            return new Placed(offered.map(each ->
                    !(Counts.writtenIn(each.value()) instanceof Place at) || within.admits(at)
                            ? each : null), everyValue);
        }

        /** These first, and where they are not every value, {@code otherwise} after them, each
         *  value once. */
        Proposals before(Supplier<Proposals> otherwise) {
            if (everyValue) {
                return offered;
            }
            Proposals.Gathering out = Proposals.Gathering.distinct();
            out.addAll(offered);
            out.addAll(otherwise.get());
            return out.done();
        }
    }

    /**
     * {@code otherwise}, the values a builder would offer at a place of {@code type}, with what the
     * place divides into under its rules put first ({@link #placed}) — and alone, where that is
     * every value the place can hold.
     *
     * <p>Only where the place's rules say which values stand there. Where they say nothing, the
     * place divides into what its type does, which is what a builder already offers.
     */
    static Proposals firstWhatThePlaceAdmits(Type type, FieldDomains.ConstructionLimits limits,
                                             RuleReadingContext reading,
                                             Set<TypeSymbol> expanding,
                                             Supplier<Proposals> otherwise) {
        if (limits.admits().approximation().isAny()) {
            return otherwise.get();
        }
        return placed(type, limits.admits(), reading, expanding).within(limits.values())
                .before(otherwise);
    }

    /** Whether {@code admitted} names the values it leaves, and some of them. */
    private static boolean namesFinitelyMany(AdmissibleSet admitted) {
        return admitted.approximation() instanceof ValueSet.Finite finite
                && !finite.values().isEmpty();
    }

    /**
     * The {@code index}th value of {@code type} made by stepping its carrier, or nothing where the
     * carrier has no order to step — or where the step is a string longer than a proposal holds,
     * which meets that figure.
     *
     * <p>A string grows by a character from the length its rules ask for, and a whole number steps
     * through the range they leave. Which characters is a question the carrier has no answer to, so
     * a type whose rules say which of them is answered before this is reached
     * ({@link Partitions#admittedStrings}) and what is left here is the length.
     *
     * <p>A date or a record has no such step that keeps every rule the
     * position carries, and inventing one would put a value in a row the type's own chooser had reason
     * not to offer — which is what the values a type divides into are for, above.
     */
    private static Proposals varied(Type type, int index, RuleReadingContext reading) {
        RuleReadingSource ruleSource = reading.source();
        TypeView view = TypeView.of(type, ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums());
        if (view.shape() instanceof Shape.Scalar scalar && scalar.prim() == Type.Prim.STRING) {
            // The floor asked first, so that a floor past the figure is not added to.
            int least = Math.max(1, Partitions.leastHeld(view, reading));
            CompositionBudget past = pastTheCharacters(least) != null
                    ? pastTheCharacters(least) : pastTheCharacters(least + index);
            return past != null ? Proposals.stoppedBy(past) : Proposals.ofNullable(WornNames.under(
                    view.wrappers(), FixtureTemplate.string("x".repeat(least + index)),
                    ruleSource));
        }
        Place at = Partitions.numberInside(view, reading, index);
        if (at == null) {
            return Proposals.NONE;
        }
        Carrier carrier = view.shape() instanceof Shape.Scalar scalar
                && scalar.prim() == Type.Prim.DECIMAL ? Carrier.DENSE : Carrier.WHOLE;
        return Proposals.ofNullable(WornNames.under(view.wrappers(), FixtureTemplate.on(
                carrier, at, ruleSource.symbols().scope()::reach), ruleSource));
    }

    private Witnesses() {}
}
