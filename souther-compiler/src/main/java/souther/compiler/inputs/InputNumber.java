package souther.compiler.inputs;

import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DateShifts;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.ElementAnswer;
import souther.compiler.check.NewtypeInners;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.SeededWalk;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.WalkElements;
import souther.compiler.core.Core;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.ValueTransformation;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * Which number of a behavior's input an expression names, or nothing where it names none.
 *
 * <p>The companion of {@link InputPath}, one question further in. That answers which location an
 * expression points at; this answers which number a rule about it is written on, which is the
 * location's own content or something taken of it — and the two are not the same answer, because a
 * position holding a string is a position holding no number while every rule about its length is
 * about one.
 *
 * <p>One answer, for every reader that has to say which number a comparison is about. The reading
 * that draws lines and the reading that names what a run was steered by both ask it, and each
 * working it out for itself is two accounts of one number: matched afterwards by how a path is
 * spelled, two numbers taken of one location are one, which is the whole of what a line drawn on
 * the second of them is lost to.
 *
 * <p>Which of the standard library's calls take a number of a location is asked of
 * {@link NumericMeasures} rather than decided here, and asked of the operation the call resolved to
 * rather than of its spelling.
 */
public final class InputNumber {

    private InputNumber() {
    }

    /**
     * The number {@code e} names, as one of the numbers a comparison is read of: none where it
     * names an element of a container that another name stands for in {@code met}.
     *
     * <p>The way in for a reader that puts numbers into one form. A form holds a number once, so
     * two names for two elements of one container, which are one position, would be merged into it.
     */
    public static NumericTerm of(Core e, InputDomain inputs, InputReads reads,
                                 RuleReadingSource source, ElementsMet met) {
        return met.admits(e, reads, source.newtypes())
                ? ofAlone(e, inputs, reads, source) : null;
    }

    /**
     * The numbers {@code e} is made of, as the one form they add up to, for a reader that puts
     * numbers into one form: the number {@link #of} names, or — where it names none — the form of
     * two numbers of a string that a total of its weighed code points comes to.
     *
     * <p>The one place that says which numbers an expression is made of, so that a reader of forms
     * does not hold a case of its own. A reader of one number at a time ({@link #ofAlone}) draws
     * a line on a single number and reads no form of two.
     */
    public static LinearForm<NumericTerm> formOf(Core e, InputDomain inputs, InputReads reads,
                                                 RuleReadingSource source, ElementsMet met) {
        NumericTerm term = of(e, inputs, reads, source, met);
        if (term != null) {
            return LinearForm.atom(term);
        }
        return met.admits(e, reads, source.newtypes())
                ? codePointsWeighed(e, inputs, reads, source) : null;
    }

    /**
     * The number {@code e} names, for a reader that asks of a side by itself and combines no two
     * numbers into one form: a line drawn on one position against a value written out.
     *
     * <p>The argument of a taking has to be a location: {@code List.length(List.map(f, xs))} counts
     * something no path names, and a boundary on it could not be looked for in a row.
     */
    public static NumericTerm ofAlone(Core e, InputDomain inputs, InputReads reads,
                                      RuleReadingSource source) {
        Symbols symbols = source.symbols();
        NumericMeasures.Measured measured = NumericMeasures.takenIn(e, symbols,
                each -> reads.folded(each, symbols, source.newtypes()));
        if (measured != null) {
            // A taking is of a location, or of what a location's value was moved into, so an
            // argument that is neither is one there is no location to take it of.
            ObservationSource of = sourceOf(measured, reads, source);
            if (of != null) {
                return NumericTerm.TakenOf.of(measured.operation(), of, measured.arguments(),
                        inputs.typeAt(of.position(), source), source.inners(), symbols);
            }
            // A total of the code points of a string standing somewhere is a number of that string.
            NumericTerm ofAString = codePointsAddedUp(measured, inputs, reads, source);
            if (ofAString != null) {
                return ofAString;
            }
            // A location the operation is not taken of, or a value standing at none. The second is
            // a walk's answer, and a number over the values it walked is a term of its own where
            // those values are read from a place.
            return overARun(measured, inputs, reads, source);
        }
        // And a number of the input is the value at a position, so an expression naming none names
        // no number here.
        return switch (reads.pathOf(e, source.newtypes())) {
            case PathResolution.At(var at) -> new NumericTerm.ValueOf(at);
            case PathResolution.NotAPosition _ -> null;
            // And a number of the input is the value at one position. A name standing at one of
            // several would be a number at whichever of them a reader picked, and a line drawn on
            // it would fall at a place the rule may say nothing about.
            case PathResolution.MayStandAt _ -> null;
        };
    }

    /**
     * The value a taking is of: the one standing at a location, one a chain of shifts of a date
     * written out made of it, or — for a number that does not turn on the order of the elements —
     * the container whose every element it holds, each as often. Null where it is none of these.
     *
     * <p>A location is asked first and is what a taking is of wherever it is one. A call that is no
     * location is then asked what the library says of it ({@link DateShifts}), so that a date moved
     * by days is a value of the place it was moved from and not a place of its own: a name that
     * only may stand at a location is still no one of them. And {@code List.reverse(xs)} adds up to
     * what {@code xs} does, so its total is the term of {@code xs} and not a second one for the
     * same number; a list that keeps some of the elements holds no container's every element.
     */
    private static ObservationSource sourceOf(NumericMeasures.Measured measured, InputReads reads,
                                              RuleReadingSource source) {
        Core of = measured.of();
        return switch (reads.pathOf(of, source.newtypes())) {
            case PathResolution.At(var at) -> ObservationSource.asItStands(at);
            case PathResolution.NotAPosition _ -> {
                ObservationSource moved = movedFromALocation(of, reads, source);
                if (moved != null || !measured.takenAs().theSameInEveryOrder()) {
                    yield moved;
                }
                TermPath reordered = reads.containerWhoseEveryElementIsIn(of, source.newtypes());
                yield reordered == null ? null : ObservationSource.asItStands(reordered);
            }
            // A taking is of one location, and a name that only may stand at one is no one of
            // them. Taken of any, the number would be a size of a container the run it is on
            // never walked.
            case PathResolution.MayStandAt _ -> null;
        };
    }

    /** {@code met} as a shift of a date by a count written out, read where it stands
     *  ({@link DateShifts#stepOf}), or null where it is none. */
    private static DateShifts.Step shiftOf(Denotation met, RuleReadingSource source) {
        return DateShifts.stepOf(met.value(),
                each -> met.at().folded(each, source.symbols(), source.newtypes()));
    }

    /**
     * The location a chain of shifts of a date starts from and what the chain comes to, or null
     * where {@code of} is no shift of a date or what it shifts is no location.
     *
     * <p>Each step is read where the date inside it stands, since a name given a shifted date is
     * the shift and the binding is where its date is read.
     */
    private static ObservationSource movedFromALocation(Core of, InputReads reads,
                                                        RuleReadingSource source) {
        // A shift of a date answers a date, so anything else is no chain and the walk below, which
        // resolves names, is not spent on it.
        if (!Type.DATE.equals(Core.withoutStanding(of).type())) {
            return null;
        }
        Symbols symbols = source.symbols();
        List<Long> days = new ArrayList<>();
        Denotation met = reads.denotes(of, symbols, source.newtypes());
        for (DateShifts.Step step = shiftOf(met, source); step != null;
                step = shiftOf(met, source)) {
            days.add(step.days());
            met = met.at().denotes(step.date(), symbols, source.newtypes());
        }
        if (days.isEmpty()
                || !(met.at().pathOf(met.value(), source.newtypes())
                        instanceof PathResolution.At(var from))) {
            return null;
        }
        // The innermost shift first: each one is defined only at the dates the ones inside it
        // leave, which is what the translation keeps and the days alone would not.
        DateTranslation translation = DateTranslation.none();
        for (Long each : days.reversed()) {
            translation = translation.thenAddDays(each);
            if (translation == null) {
                return null;
            }
        }
        return new ObservationSource(from, ValueTransformation.of(translation));
    }

    /**
     * What the code points of a string at a location come to, where {@code measured} totals what an
     * operation lists of them — or null where it is anything else.
     *
     * <p>Two statements and each is the library's: that the operation measured adds up what a
     * container holds, and that the list it is handed is the string's code points, each the number
     * it is. The list is followed through the names and the helpers it was handed through, as a
     * walk is, so a total of a list bound to a name first is the same number of the same string.
     */
    private static NumericTerm codePointsAddedUp(NumericMeasures.Measured measured,
                                                 InputDomain inputs, InputReads reads,
                                                 RuleReadingSource source) {
        if (!measured.arguments().none()
                || !(measured.takenAs() instanceof TakenAs.TheSumOfWhatItHolds)) {
            return null;
        }
        TermPath at = stringWhoseCodePointsAre(measured.of(), reads, source);
        return at == null ? null
                : NumericTerm.CodePointValueSum.of(at, inputs.typeAt(at, source), source.inners());
    }

    /** The location of the string whose code points {@code listed} lists, or null where it lists
     *  those of no string standing at one. */
    private static TermPath stringWhoseCodePointsAre(Core listed, InputReads reads,
                                                     RuleReadingSource source) {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        Denotation standing = reads.standing(listed, source.symbols(), source.newtypes());
        AnOperationApplied applied = AnOperationApplied.of(standing.value());
        DeclaredArgument string = applied == null ? null
                : facts.codePointsListedOf(applied.operation());
        Core argument = string == null ? null : applied.argument(string);
        return argument != null && standing.at().pathOf(argument, source.newtypes())
                instanceof PathResolution.At(var at) ? at : null;
    }

    /**
     * What a total of a closure applied to each code point of a string comes to, where the closure
     * is {@code weight·x + constant} of the code point {@code x}: that weight times the total of the
     * code points, and that constant times how many there are.
     *
     * <p>The code points are the elements of a list no row writes, so there is no position of an
     * element to read the closure at, and the number is of the string at one position. What the
     * closure makes of a code point is read as it is of an element of an input list, for elements
     * that stand at no place ({@link ElementValue#readWithoutAPlace}). Null where the walk keeps some of the elements, where the closure
     * turns on where an element stands or on anything but the code point, or where the total is of
     * something else.
     *
     * <p>That the walk answers one value per code point is the licence the walk's closure carries
     * ({@link InputReads#answerAt}), which the operation's declaration gives only to a walk whose
     * result holds one answer of the closure per element ({@code BuiltFrom#mapsEachElementOf}).
     * The binding the closure is handed its element on says nothing of that: {@code List.sortBy}
     * hands its closure the elements too, and what it computes is a key, not a term of the total.
     */
    private static LinearForm<NumericTerm> codePointsWeighed(Core e, InputDomain inputs,
                                                             InputReads reads,
                                                             RuleReadingSource source) {
        Symbols symbols = source.symbols();
        NumericMeasures.Measured measured = NumericMeasures.takenIn(e, symbols,
                each -> reads.folded(each, symbols, source.newtypes()));
        if (measured == null || !measured.arguments().none()
                || !(measured.takenAs() instanceof TakenAs.TheSumOfWhatItHolds)) {
            return null;
        }
        Denotation walked = reads.denotes(measured.of(), symbols, source.newtypes());
        while (walked != null) {
            LinearForm<NumericTerm> weighed = weighedByTheWalk(walked, inputs, source);
            if (weighed != null) {
                return weighed;
            }
            walked = walked.at().stepKeepingEveryElement(walked, symbols, source.newtypes());
        }
        return null;
    }

    private static LinearForm<NumericTerm> weighedByTheWalk(Denotation walked, InputDomain inputs,
                                                            RuleReadingSource source) {
        InputReads where = walked.at();
        BindingId element = WalkElements.elementBindingOf(walked.value(), where, source.symbols(),
                source.newtypes());
        Core listed = element == null ? null : where.containerOfTheElementHandedTo(element);
        TermPath at = listed == null ? null : stringWhoseCodePointsAre(listed, where, source);
        ElementAnswer closure = at == null ? null : where.answerAt(element);
        if (closure == null) {
            return null;
        }
        ElementValue computed =
                ElementValue.readWithoutAPlace(closure, where.heldByTheBody(), source);
        if (!(computed instanceof ElementValue.Affine(var form))) {
            return null;
        }
        ElementProjection codePoint = new ElementProjection(List.of());
        if (!form.coefs().keySet().stream().allMatch(codePoint::equals)) {
            return null;
        }
        Type string = inputs.typeAt(at, source);
        NumericTerm sum = NumericTerm.CodePointValueSum.of(at, string, source.inners());
        NumericTerm length = NumericTerm.TakenOf.howManyHeldAt(
                ValueName.Stdlib.operation("String", "length"), at, string, source.inners(),
                source.symbols());
        if (sum == null || length == null) {
            return null;
        }
        Map<NumericTerm, ExactRatio> weights = new LinkedHashMap<>();
        ExactRatio weight = form.coefs().getOrDefault(codePoint, ExactRatio.ZERO);
        if (!weight.isZero()) {
            weights.put(sum, weight);
        }
        if (!form.constant().isZero()) {
            weights.put(length, form.constant());
        }
        return new LinearForm<>(ExactRatio.ZERO, weights);
    }

    /**
     * The number {@code measured} takes over the values a walk was given, or null where those
     * values are not read from a place.
     *
     * <p>Three answers have to be in hand, and each is somebody else's. That the walk answers one
     * value per element of what it was given is a fact about the operation that handed the closure
     * its elements, proved before the tree was rewritten. Where in an element the answer stands is
     * what the closure came to, read once and kept as the way there. And which position the
     * elements are at is the reading of the input's, as it is for every other term.
     *
     * <p>What the walk itself supplies is the element's binding and nothing more. The form it has
     * now is what a rewrite left, so it is asked for an identity and not for a meaning: reading the
     * answer off the shape would make the walks a rule can be written over a consequence of which
     * ones that rewrite happens to recognise, and a walk an author wrote by hand would be read as
     * a {@code map}.
     *
     * <p>The walk is met under whatever name is in scope, and what a name stands for is asked of
     * the reading that owns the question ({@link InputReads#meaningOf}) rather than read off the
     * tree. A model of any size binds the mapped list before totalling it, and a route that walked
     * only the expression as written would answer one thing for
     * {@code List.sum(List.map(f, xs))} and another for the same rule with a name in the middle —
     * which is a `let` changing what a model means. The environment the value was given in comes
     * with it, so what is read of the walk afterwards is read where the walk stands.
     *
     * <p>Where the answer is no place of the element but something made of its fields, the run is
     * over what was computed of each element instead ({@link #overWhatWasComputed}), and is the run
     * over a place where what was computed is that place.
     *
     * <p>Null wherever any of the three is missing, which is a rule this compiler did not read
     * rather than a rule the model does not state — and is reported as one. Null too where the three
     * are in hand and what they come to is not one run
     * ({@link RunSource#overEveryOccurrenceAt}), which is the same answer for the same reason: a
     * reading short rather than a line somewhere it does not go.
     */
    private static NumericTerm overARun(NumericMeasures.Measured measured, InputDomain inputs,
                                        InputReads reads, RuleReadingSource source) {
        Symbols symbols = source.symbols();
        // A number over a run is named by the operation and where the values are read from, and a
        // taking given a value beside them is a number those two do not name. Read without it, the
        // total of one part of each element would be the total of another.
        if (!measured.arguments().none()) {
            return null;
        }
        // The walk and the names it stands under, which travel together: a name bound inside a
        // helper stands for what the call handed over, and what is read of that afterwards is read
        // where it stands rather than where the name was.
        Denotation met = reads.denotes(measured.of(), symbols, source.newtypes());
        // What puts the values in another order, or answers each as it is, beside the walk that
        // makes them is the same total: where the outermost operation is no walk over a place, the
        // one beneath it is asked.
        while (met != null) {
            NumericTerm run = overTheRunWalkedBy(measured, met, inputs, source);
            if (run != null) {
                return run;
            }
            met = met.at().stepKeepingEveryElement(met, symbols, source.newtypes());
        }
        return null;
    }

    /** The number {@code measured} takes over the values the walk {@code met} was given
     *  ({@link #overARun}), or null where those values are not read from a place. */
    private static NumericTerm overTheRunWalkedBy(NumericMeasures.Measured measured,
                                                  Denotation met, InputDomain inputs,
                                                  RuleReadingSource source) {
        Symbols symbols = source.symbols();
        Core walk = met.value();
        InputReads where = met.at();
        BindingId element =
                WalkElements.elementBindingOf(walk, where, symbols, source.newtypes());
        if (element == null) {
            return null;
        }
        ElementProjection answered = where.projectionAt(element);
        // Where the elements stand, every one of them once, and nothing where they stand nowhere:
        // a run is over the values at a position, so a container this reading could not place
        // leaves no run to take — and a walk over some of them, as one after a filter is, is no
        // run over the values standing there.
        TermPath at = switch (where.everyElementAt(element, source.newtypes())) {
            case PathResolution.At(var stands) -> stands;
            case PathResolution.NotAPosition _ -> null;
            // A run is over the values at one position, and a walk whose elements come from more
            // than one container is no one run.
            case PathResolution.MayStandAt _ -> null;
        };
        if (at == null) {
            return null;
        }
        ElementValue computed = null;
        if (answered == null) {
            // A total of how many a container inside each element holds is how many occurrences
            // of its element there are — where the elements walked are those of a container no
            // other holds. One inside another is one of many, and every occurrence of the path is
            // under every one of them.
            ElementProjection counted = countedOfEach(measured, where, element, source);
            if (counted != null && at.containersHoldingIt().size() == 1) {
                return howManyStandAt(counted.from(at).element(), inputs, source);
            }
            computed = computedOf(measured, where, element, source,
                    new ElementValue.ElementsAt(at, where.declared()));
            if (computed == null) {
                return null;
            }
            // What was computed may be the element's own field and nothing made of it, as a closure
            // that weighs a field once and adds nothing is. That is the place, and one number has
            // one term whichever way its closure was spelled.
            answered = placeStanding(computed, where.answerAt(element), at, inputs, source);
        }
        if (answered == null) {
            // A number that turns on where each element stands is a number of them in the order
            // the row writes them, which is asked as well and only then.
            RunSource.TraversalOrder order = computed.readsThePosition()
                    ? theOrderTheWalkWasHandedThem(where, element, at, source) : null;
            return overWhatWasComputed(measured, where.answerAt(element), computed, at, order,
                    source);
        }
        TermPath under = answered.from(at);
        // Every occurrence of the elements' position, so every occurrence of the place in them:
        // one run where one container holds them, and the lists of an outer list put end to end
        // where several do.
        RunSource over = RunSource.overEveryOccurrenceAt(under);
        if (over == null) {
            return null;
        }
        Type stands = inputs.typeAt(under, source);
        return stands == null ? null
                : NumericTerm.TakenOver.of(measured.operation(), over, stands, source.inners(),
                        symbols);
    }

    /**
     * What a walk from a seed answers where its step only adds to the answer so far: the seed and
     * what the step adds over every element.
     *
     * @param seed  what the walk starts from
     * @param added what the step adds over every element: the total of what it adds of each, the
     *              term {@code List.sum} of the same values is, or — where it adds the same for
     *              each — that many times how many elements there are; nothing where it adds none
     */
    public record SeedAndAdded(ExactRatio seed, LinearForm<NumericTerm> added) {}

    /**
     * What {@code e} is, where it is a walk from a seed ({@link SeededWalk}) whose step answers the
     * answer so far and something of the element alone: the seed, and the total of those somethings
     * over the elements at one position. Null where it is any other walk, or where the elements are
     * not read from a place.
     *
     * <p>By induction over the walk, which visits every element of what it walks once — that is
     * what the library's one loop does, and what the walks defined over it hand it — the answer is
     * {@code seed + Σ w(x)} where the step is {@code 1·answer + w(x)}. That is asked of the step as
     * a form of the answer so far and the element's fields together ({@link
     * ElementValue#addedTo}), so a step is accepted where the arithmetic composes it that way and
     * for every answer. {@code acc + x}, {@code x + acc} and {@code Decimal.add(acc, x)} are one
     * step; a step that is merely right at some answers, like {@code acc * acc + x} at nought and
     * at one, is none.
     *
     * <p>The total is the term {@code List.sum} of those values is, so a rule over a fold and a rule
     * over a sum of the same numbers are about one number.
     *
     * @param blockOf the block a closure argument stands for, where the call stands
     */
    public static SeedAndAdded ofAWalkAdding(Core e, InputDomain inputs, InputReads reads,
                                             RuleReadingSource source,
                                             Function<Core, Core.Block> blockOf) {
        SeededWalk walk = SeededWalk.of(e, blockOf);
        if (walk == null) {
            return null;
        }
        Denotation container =
                reads.standing(walk.container(), source.symbols(), source.newtypes());
        // Every occurrence of the position and each as often, which a total of what each element
        // adds is a total of.
        if (!(container.at().everyElementOf(container.value(), source.newtypes())
                instanceof PathResolution.At(TermPath at))) {
            return null;
        }
        BindingId element = walk.element().binding();
        Map<BindingId, Core> held = reads.heldByTheBody();
        ElementValue.ElementsAt elements =
                new ElementValue.ElementsAt(at, container.at().declared());
        ElementValue.Added step = ElementValue.addedTo(
                new ElementAnswer(element, walk.step().body(), null), walk.accumulator().binding(),
                held, source, elements);
        ElementValue.Affine seed = affine(ElementValue.read(
                new ElementAnswer(element, walk.seed(), null), held, source, elements));
        if (step == null || seed == null || !seed.form().coefs().isEmpty()) {
            return null;
        }
        Map<NumericTerm, ExactRatio> added = new LinkedHashMap<>();
        // How many a container inside each element holds, over every element, is how many
        // occurrences of its element there are.
        for (Map.Entry<ElementProjection, ExactRatio> counted : step.heldAt().entrySet()) {
            NumericTerm howMany =
                    howManyStandAt(counted.getKey().from(at).element(), inputs, source);
            if (howMany == null) {
                return null;
            }
            added.put(howMany, counted.getValue());
        }
        ElementValue adds = step.ofTheElement();
        if (adds instanceof ElementValue.Affine alike && alike.form().coefs().isEmpty()) {
            // What every element adds alike is that many for each of them, so a step adding
            // nothing else of the element counts them.
            ExactRatio each = alike.form().constant();
            if (each.signum() != 0) {
                NumericTerm howMany = howManyStandAt(at, inputs, source);
                if (howMany == null) {
                    return null;
                }
                added.put(howMany, each);
            }
            return new SeedAndAdded(seed.form().constant(),
                    new LinearForm<>(ExactRatio.ZERO, added));
        }
        ElementProjection place = adds.asAPlace();
        NumericTerm total;
        if (place != null && step.heldAt().isEmpty() && TypeOps.base(walk.step().body().type(),
                source.inners()).equals(TypeOps.base(inputs.typeAt(place.from(at), source),
                source.inners()))) {
            RunSource over = RunSource.overEveryOccurrenceAt(place.from(at));
            total = over == null ? null
                    : NumericTerm.TakenOver.of(SUM, over, inputs.typeAt(place.from(at), source),
                            source.inners(), source.symbols());
        } else {
            Type each = walk.step().body().type();
            RunSource over = RunSource.computedOverTheElementsAt(at, adds, each, null);
            total = over == null ? null
                    : NumericTerm.TakenOver.of(SUM, over, each, source.inners(), source.symbols());
        }
        if (total == null) {
            return null;
        }
        added.put(total, ExactRatio.ONE);
        return new SeedAndAdded(seed.form().constant(), new LinearForm<>(ExactRatio.ZERO, added));
    }

    /**
     * How many values {@code run}, one no single container holds, holds — or null where it is
     * one container's, whose count is a taking of that container's place.
     *
     * @param each what stands where the run's values are read from
     */
    public static NumericTerm.TakenOver howManyHeld(RunSource run, Type each,
                                                    RuleReadingSource source) {
        return NumericTerm.TakenOver.howManyOf(run, each, source.inners(), source.symbols());
    }

    /**
     * How many values stand at {@code every}, every occurrence of a place inside some container:
     * the size of that container where it is one, and the count of the run over all of them where
     * it is inside several — or null where neither is a number this reads.
     */
    public static NumericTerm howManyStandAt(TermPath every, InputDomain inputs,
                                             RuleReadingSource source) {
        RunSource run = RunSource.overEveryOccurrenceAt(every);
        if (run == null) {
            return null;
        }
        if (!run.isInOneContainer()) {
            return howManyHeld(run, inputs.typeAt(every, source), source);
        }
        TermPath container = every.containersHoldingIt().getLast();
        Type held = inputs.typeAt(container, source);
        ValueName.Stdlib measure = held == null ? null
                : NumericMeasures.takenOf(held, source.inners());
        return measure == null ? null
                : NumericTerm.TakenOf.of(measure, ObservationSource.asItStands(container),
                        TakenArguments.NONE, held, source.inners(), source.symbols());
    }

    private static final ValueName.Stdlib.Operation SUM =
            ValueName.Stdlib.operation("List", "sum");

    /**
     * What the closure the elements of a list a dependency answered were handed to computes of one
     * of them, where it turns on where the element stands in the list — or null where it does not,
     * or is not read.
     *
     * <p>The elements stand at no position of the input, so it is read as the code points of a
     * string are ({@link ElementValue#readWithoutAPlace}). A computation that does not turn on the
     * position is a sum of the elements' own numbers, which the answer's sums already say.
     */
    public static ElementValue computedByPositionOfAnAnswersElement(ElementAnswer closure,
                                                                    InputReads reads,
                                                                    RuleReadingSource source) {
        ElementValue computed =
                ElementValue.readWithoutAPlace(closure, reads.heldByTheBody(), source);
        return computed != null && computed.readsThePosition() ? computed : null;
    }

    /**
     * The number {@code operation} takes of what {@code computed} makes of each element of the list
     * at {@code list}, handed in {@code direction} — the term a total of the same computation over a
     * list of the input is — or null where the elements are not one run.
     */
    public static NumericTerm overWhatWasComputedByPosition(ValueName.Stdlib operation,
                                                            TermPath list, ElementValue computed,
                                                            Type each, TraversalDirection direction,
                                                            NewtypeInners inners,
                                                            Symbols symbols) {
        TermPath elements = list.element();
        RunSource over = RunSource.computedOverTheElementsAt(elements, computed, each,
                new RunSource.TraversalOrder(elements, direction));
        return over == null ? null : NumericTerm.TakenOver.of(operation, over, each, inners, symbols);
    }

    private static ElementValue.Affine affine(ElementValue read) {
        return read instanceof ElementValue.Affine form ? form : null;
    }

    /**
     * The field {@code computed} is, where it is that field as the same kind of number, or null.
     *
     * <p>The same number is not the same term. What a total is counted as is part of it, and a call
     * that changes only that — whole numbers as decimals — computes the field's number and is not
     * the field: two lines of the largest whole number come to a decimal and to no whole number.
     * So a form that is a field is the place only where what the closure answers stands as what the
     * field stands as, with the names either is written under taken off, which is the account the
     * term is made under ({@link NumericTerm.TakenOver#of}).
     */
    private static ElementProjection placeStanding(ElementValue computed, ElementAnswer closure,
                                                   TermPath at, InputDomain inputs,
                                                   RuleReadingSource source) {
        ElementProjection place = computed.asAPlace();
        if (place == null) {
            return null;
        }
        Type fieldType = inputs.typeAt(place.from(at), source);
        return fieldType != null && TypeOps.base(closure.body().type(), source.inners())
                .equals(TypeOps.base(fieldType, source.inners())) ? place : null;
    }

    /**
     * The direction the walk was handed the elements at {@code at} in, as the row writes them or
     * from the last to the first, whichever the reading of the input shows — or null where it shows
     * neither.
     */
    private static RunSource.TraversalOrder theOrderTheWalkWasHandedThem(
            InputReads where, BindingId element, TermPath at, RuleReadingSource source) {
        for (TraversalDirection direction : TraversalDirection.values()) {
            if (where.inTheOrderAt(element, direction, source.newtypes())
                    instanceof PathResolution.At(TermPath shown) && shown.equals(at)) {
                return new RunSource.TraversalOrder(at, direction);
            }
        }
        return null;
    }

    /**
     * The number {@code measured} takes over what a walk computed of each of its elements, or null
     * where the walk answered no such computation this reads.
     *
     * <p>For a closure whose answer is not a place of its element — arithmetic over its fields, a
     * choice between two of those by a flag it holds, or a choice among them by the case a value of
     * it is. The licence is the one a place answer has:
     * the walk answers one value per element of what it was given, proved before the tree was
     * rewritten, so what is asked here is only what the closure came to.
     */
    private static NumericTerm overWhatWasComputed(NumericMeasures.Measured measured,
                                                   ElementAnswer closure, ElementValue computed,
                                                   TermPath at, RunSource.TraversalOrder order,
                                                   RuleReadingSource source) {
        Type each = closure.body().type();
        RunSource over = RunSource.computedOverTheElementsAt(at, computed, each, order);
        return over == null ? null
                : NumericTerm.TakenOver.of(measured.operation(), over, each, source.inners(),
                        source.symbols());
    }

    /**
     * The place of the element whose container the closure the walk handed {@code element} to
     * counts, where {@code measured} is a total of those counts — or null where it is anything
     * else.
     */
    private static ElementProjection countedOfEach(NumericMeasures.Measured measured,
                                                   InputReads where, BindingId element,
                                                   RuleReadingSource source) {
        if (!(measured.takenAs() instanceof TakenAs.TheSumOfWhatItHolds)) {
            return null;
        }
        ElementAnswer closure = where.answerAt(element);
        return closure == null ? null : ElementValue.countedAt(closure.body(),
                closure.parameter(), where.heldByTheBody(), source);
    }

    /**
     * What the closure the walk handed {@code element} to computed of it, or null where there is no
     * such closure or this reads none of it.
     *
     * <p>Only for a total. What is read of a run computed of each element is the sum of those
     * numbers; a count of a walk's answers is a count of the container it walked, and is read as
     * that.
     */
    private static ElementValue computedOf(NumericMeasures.Measured measured, InputReads where,
                                           BindingId element, RuleReadingSource source,
                                           ElementValue.ElementsAt elements) {
        if (!(measured.takenAs() instanceof TakenAs.TheSumOfWhatItHolds)) {
            return null;
        }
        ElementAnswer closure = where.answerAt(element);
        return closure == null ? null
                : ElementValue.read(closure, where.heldByTheBody(), source, elements);
    }

}
