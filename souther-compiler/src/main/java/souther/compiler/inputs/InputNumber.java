package souther.compiler.inputs;

import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DateShifts;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.ElementAnswer;
import souther.compiler.check.ElementsWrittenOut;
import souther.compiler.check.NewtypeInners;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.SeededWalk;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.WalkElements;
import souther.compiler.core.Core;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.ValueTransformation;
import souther.compiler.semantics.PieceOfAnElement;
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
        if (!met.admits(e, reads, source.newtypes())) {
            return null;
        }
        LinearForm<NumericTerm> form = formAlone(e, inputs, reads, source);
        return form != null ? form : codePointsWeighed(e, inputs, reads, source);
    }

    /**
     * The number {@code e} names, for a reader that asks of a side by itself and combines no two
     * numbers into one form: a line drawn on one position against a value written out.
     *
     * <p>The argument of a taking has to be a location: {@code List.length(List.map(f, xs))} counts
     * something no path names, and a boundary on it could not be looked for in a row.
     *
     * <p>One number, so where {@code e} comes to a form of several or to a number written out —
     * a total of three for each element is three times how many there are — it names none here,
     * and a reader of forms ({@link #formOf}) reads it.
     */
    public static NumericTerm ofAlone(Core e, InputDomain inputs, InputReads reads,
                                      RuleReadingSource source) {
        return alone(formAlone(e, inputs, reads, source));
    }

    /** What {@code e} comes to, as {@link #ofAlone} reads it but held as the form it is. */
    private static LinearForm<NumericTerm> formAlone(Core e, InputDomain inputs, InputReads reads,
                                                     RuleReadingSource source) {
        Symbols symbols = source.symbols();
        NumericTerm steps = wholeUnitsOf(e, inputs, reads, source);
        if (steps != null) {
            return LinearForm.atom(steps);
        }
        NumericMeasures.Measured measured = NumericMeasures.takenIn(e, symbols,
                each -> reads.folded(each, symbols, source.newtypes()));
        if (measured != null) {
            // A taking is of a location, or of what a location's value was moved into, so an
            // argument that is neither is one there is no location to take it of.
            ObservationSource of = sourceOf(measured, reads, source);
            if (of != null) {
                return atomOf(NumericTerm.TakenOf.of(measured.operation(), of,
                        measured.arguments(), inputs.typeAt(of.position(), source),
                        source.inners(), symbols));
            }
            // A total of the code points of a string standing somewhere is a number of that string.
            NumericTerm ofAString = codePointsAddedUp(measured, inputs, reads, source);
            if (ofAString != null) {
                return LinearForm.atom(ofAString);
            }
            // A location the operation is not taken of, or a value standing at none. The second is
            // a walk's answer, and a number over the values it walked is a term of its own where
            // those values are read from a place.
            return overARun(measured, inputs, reads, source);
        }
        // An element an index picks of a list of a string's code points is the code point at the
        // index of the string that stands there.
        InputReads.PickedAtAnIndex picked = reads.pickedAtAnIndex(e);
        NumericTerm codePoint = picked == null ? null : codePointPicked(picked, inputs, source);
        if (codePoint != null) {
            return LinearForm.atom(codePoint);
        }
        // And a number of the input is the value at a position, so an expression naming none names
        // no number here.
        return switch (reads.pathOf(e, source.newtypes())) {
            case PathResolution.At(var at) -> LinearForm.atom(new NumericTerm.ValueOf(at));
            case PathResolution.NotAPosition _ -> null;
            // And a number of the input is the value at one position. A name standing at one of
            // several would be a number at whichever of them a reader picked, and a line drawn on
            // it would fall at a place the rule may say nothing about.
            case PathResolution.MayStandAt _, PathResolution.MadeOf _ -> null;
        };
    }

    /**
     * The step of a coarser order that the value at a location falls in, where {@code e} is a call
     * of an operation counting whole units, or null where it is none.
     *
     * <p>Of a location only: the date of a date-time made of other arithmetic names no position a
     * row could be asked to hold.
     */
    private static NumericTerm wholeUnitsOf(Core e, InputDomain inputs, InputReads reads,
                                            RuleReadingSource source) {
        Denotation standing = reads.standing(e, source.symbols(), source.newtypes());
        AnOperationApplied applied = AnOperationApplied.of(standing.value());
        Core counted = DefaultBoundOperationFacts.get().wholeUnitsCountedIn(applied);
        if (counted == null || !(standing.at().pathOf(counted, source.newtypes())
                instanceof PathResolution.At(var at))
                || !(applied.operation() instanceof ValueName.Stdlib operation)) {
            return null;
        }
        return NumericTerm.WholeUnitsOf.of(operation, at, inputs.typeAt(at, source),
                source.inners(), source.declarations());
    }

    /** {@code term} as a form of it alone, or null where there is none. */
    private static LinearForm<NumericTerm> atomOf(NumericTerm term) {
        return term == null ? null : LinearForm.atom(term);
    }

    /** The one number {@code form} is, weighed one with nothing beside it, or null where it is
     *  none or more than that. */
    private static NumericTerm alone(LinearForm<NumericTerm> form) {
        if (form == null || !form.constant().isZero() || form.coefs().size() != 1) {
            return null;
        }
        Map.Entry<NumericTerm, ExactRatio> only = form.coefs().entrySet().iterator().next();
        return only.getValue().equals(ExactRatio.ONE) ? only.getKey() : null;
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
            case PathResolution.MayStandAt _, PathResolution.MadeOf _ -> null;
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
        ElementAnswer closure = listed == null ? null : where.answerAt(element);
        ElementValue computed = closure == null ? null
                : ElementValue.readWithoutAPlace(closure, where.heldByTheBody(), source);
        if (computed == null) {
            return null;
        }
        TermPath at = stringWhoseCodePointsAre(listed, where, source);
        if (at == null || !(computed instanceof ElementValue.Affine(var form))) {
            return codePointByCodePoint(computed, listed, where, inputs, source);
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
     * What a total of what a closure computed of each code point of a string comes to, written out
     * code point by code point: {@code Σ a_k·cp(i_k) + b_k}, where the walk's {@code k}-th element
     * is the code point at {@code i_k} of the string and the closure comes to {@code a_k·c + b_k} of
     * an element {@code c} standing at {@code k} ({@link ElementValue#atPosition}).
     *
     * <p>Where how many code points the string holds is settled by its rules and no more than a
     * walk writes out ({@link ElementsWrittenOut#MOST_WALKED}), and which of them the walk is handed
     * at each place is read off what the operations between say of their elements' indices
     * ({@link #indicesOf}). Null otherwise, and where the closure at some place is no form of the
     * code point alone: a code point read through a choice of the element, or a product of two, is
     * a total this does not read rather than one it reads as numbers apart.
     */
    private static LinearForm<NumericTerm> codePointByCodePoint(ElementValue computed,
                                                                Core listed, InputReads where,
                                                                InputDomain inputs,
                                                                RuleReadingSource source) {
        CodePointsWalked walked = indicesOf(listed, where, inputs, source);
        if (walked == null) {
            return null;
        }
        Type string = inputs.typeAt(walked.at(), source);
        ElementProjection codePoint = new ElementProjection(List.of());
        ExactRatio constant = ExactRatio.ZERO;
        Map<NumericTerm, ExactRatio> weights = new LinkedHashMap<>();
        for (int k = 0; k < walked.indices().size(); k++) {
            LinearForm<ElementProjection> here = computed.atPosition(k);
            if (here == null || !here.coefs().keySet().stream().allMatch(codePoint::equals)
                    || !(constant.plus(here.constant())
                            instanceof ExactAnswer.Held<ExactRatio>(ExactRatio added))) {
                return null;
            }
            constant = added;
            ExactRatio weight = here.coefs().getOrDefault(codePoint, ExactRatio.ZERO);
            if (weight.isZero()) {
                continue;
            }
            NumericTerm.CodePointAt at = NumericTerm.CodePointAt.of(walked.at(),
                    walked.indices().get(k), string, source.inners());
            if (at == null) {
                return null;
            }
            ExactRatio before = weights.getOrDefault(at, ExactRatio.ZERO);
            if (!(before.plus(weight) instanceof ExactAnswer.Held<ExactRatio>(ExactRatio summed))) {
                return null;
            }
            if (summed.isZero()) {
                weights.remove(at);
            } else {
                weights.put(at, summed);
            }
        }
        return new LinearForm<>(constant, weights);
    }

    /**
     * The code point of a string that the element {@code picked} is, where the list is one of the
     * string's code points that {@link #indicesOf} follows and the index is within it — or null.
     */
    private static NumericTerm codePointPicked(InputReads.PickedAtAnIndex picked,
                                               InputDomain inputs, RuleReadingSource source) {
        CodePointsWalked walked = indicesOf(picked.list().value(), picked.list().at(), inputs,
                source);
        if (walked == null || picked.index() >= walked.indices().size()) {
            return null;
        }
        return NumericTerm.CodePointAt.of(walked.at(),
                walked.indices().get((int) picked.index()), inputs.typeAt(walked.at(), source),
                source.inners());
    }

    /**
     * The string a list of code points is of, and which of its code points stands at each place of
     * the list — or null where the list is no such list, or the string holds no number of code
     * points its rules settle.
     *
     * <p>Followed through the operations whose answers' elements the library says the indices of:
     * the code points of a string are its code points in order; an operation holding the elements
     * of a list by their index holds them in the order they stand there, each once, so those before
     * a written count are the first that many and those from it on are the rest
     * ({@code HoldsTheElementsByIndex}); and one answering a list's elements in the opposite order
     * holds as many, the last first. Nothing else is followed.
     */
    private static CodePointsWalked indicesOf(Core listed, InputReads where, InputDomain inputs,
                                              RuleReadingSource source) {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        Denotation standing = where.standing(listed, source.symbols(), source.newtypes());
        AnOperationApplied applied = AnOperationApplied.of(standing.value());
        if (applied == null) {
            return null;
        }
        DeclaredArgument string = facts.codePointsListedOf(applied.operation());
        if (string != null) {
            Core argument = applied.argument(string);
            if (argument == null || !(standing.at().pathOf(argument, source.newtypes())
                    instanceof PathResolution.At(var at))) {
                return null;
            }
            Integer length = howManyCodePointsAt(at, inputs, source);
            if (length == null || length > ElementsWrittenOut.MOST_WALKED) {
                return null;
            }
            List<Integer> indices = new ArrayList<>();
            for (int i = 0; i < length; i++) {
                indices.add(i);
            }
            return new CodePointsWalked(at, indices);
        }
        BoundOperationFacts.KeptByIndex kept = facts.holdsTheElementsByIndex(applied.operation());
        if (kept != null) {
            Core count = applied.argument(kept.count());
            Core list = applied.argument(kept.list());
            CodePointsWalked inner = count == null || list == null ? null
                    : indicesOf(list, standing.at(), inputs, source);
            if (inner == null || !(standing.at().folded(count, source.symbols(),
                    source.newtypes()).orElse(null) instanceof Long written)) {
                return null;
            }
            int size = inner.indices().size();
            int cut = Math.clamp(written, 0, size);
            return new CodePointsWalked(inner.at(), kept.kept() == Rel.LT
                    ? inner.indices().subList(0, cut) : inner.indices().subList(cut, size));
        }
        int reversed = DefaultBoundOperationFacts.positionOfTheArgumentReversed(
                applied.operation());
        if (reversed >= 0 && reversed < applied.args().size()) {
            CodePointsWalked inner = indicesOf(applied.args().get(reversed), standing.at(), inputs,
                    source);
            return inner == null ? null
                    : new CodePointsWalked(inner.at(), inner.indices().reversed());
        }
        return null;
    }

    /**
     * How many code points the string at {@code at} holds, where its rules settle one number:
     * what they say of its length met with the shortest and the longest string its format holds.
     * Null where they leave it more than one, or no number at all.
     */
    private static Integer howManyCodePointsAt(TermPath at, InputDomain inputs,
                                               RuleReadingSource source) {
        Position position = inputs.at(at);
        Type string = inputs.typeAt(at, source);
        NumericTerm.TakenOf length = string == null ? null : NumericTerm.TakenOf.howManyHeldAt(
                ValueName.Stdlib.operation("String", "length"), at, string, source.inners(),
                source.symbols());
        return position == null || length == null ? null : position.codePointsHeld(length);
    }

    /**
     * The string a list of code points is of, and the index of its code point at each place of
     * the list.
     */
    private record CodePointsWalked(TermPath at, List<Integer> indices) {

        private CodePointsWalked {
            indices = List.copyOf(indices);
        }
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
     * <p>Where the answer is no place of the element but something made of its fields, the number
     * is over what was computed of each element instead, and what that comes to is asked of
     * {@link #overTheElements} however the walk was written.
     *
     * <p>Null wherever any of the three is missing, which is a rule this compiler did not read
     * rather than a rule the model does not state — and is reported as one. Null too where the three
     * are in hand and what they come to is not one run
     * ({@link RunSource#overEveryOccurrenceAt}), which is the same answer for the same reason: a
     * reading short rather than a line somewhere it does not go.
     */
    private static LinearForm<NumericTerm> overARun(NumericMeasures.Measured measured,
                                                    InputDomain inputs, InputReads reads,
                                                    RuleReadingSource source) {
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
            LinearForm<NumericTerm> run = overTheRunWalkedBy(measured, met, List.of(), inputs, source);
            if (run == null) {
                run = overTheElementsKeptBy(measured, met, inputs, source);
            }
            if (run != null) {
                return run;
            }
            met = met.at().stepKeepingEveryElement(met, symbols, source.newtypes());
        }
        return null;
    }

    /**
     * The total of the elements {@code met} keeps of a list by their index — the ones before a
     * count, or the ones from it on — or null where it keeps none that way, or the count is no
     * whole number written out, or what they are kept of is not read from a place in an order.
     *
     * <p>Some of the elements, so no total of the list ({@link #sourceOf} refuses it there), and
     * which of them is fixed by where each stands: the total of each element weighed one where its
     * position passes the test the library keeps it by and nought where it does not
     * ({@link ElementValue.ByPosition}). That is a number of the elements in the order they were
     * kept in, so it is read where that order is shown, as the row writes them or from the far end.
     * A count past the last keeps every element on one side and none on the other, and a test of
     * the position says so without a case of its own. A count of nought or less keeps every
     * element or none whatever the length, which the test says of itself
     * ({@link ElementValue.PositionTest#holdsOfEveryPosition}): the total of the list, or nought.
     * A take or drop of another is read the same way ({@link #selectionByIndex}).
     *
     * <p>Kept from what a walk answered, the walk is handed the whole list and the test is of where
     * its answers stand, which is where it was handed each element. Kept from what a walk is then
     * handed, the walk would number the kept elements again from nought, so a selection under a
     * walk is not read here.
     */
    private static LinearForm<NumericTerm> overTheElementsKeptBy(
            NumericMeasures.Measured measured, Denotation met, InputDomain inputs,
            RuleReadingSource source) {
        if (!(measured.takenAs() instanceof TakenAs.TheSumOfWhatItHolds)) {
            return null;
        }
        Selection selected = selectionByIndex(met, source);
        if (selected == null) {
            return null;
        }
        Denotation listed = selected.list();
        LinearForm<NumericTerm> walked =
                overTheRunWalkedBy(measured, listed, selected.kept(), inputs, source);
        if (walked != null) {
            return walked;
        }
        ElementValue computed = keptBy(selected.kept(), new ElementValue.Affine(
                LinearForm.atom(new ElementProjection(List.of()))));
        // Kept by a test that holds of every position or of none, the number turns on no position
        // and is one of every element whatever order they stand in.
        if (!computed.readsThePosition()) {
            return listed.at().everyElementOf(listed.value(), source.newtypes())
                    instanceof PathResolution.At(TermPath at)
                    ? overTheElements(measured.operation(), measured.takenAs(), at, computed,
                            inputs.typeAt(at, source), null, inputs, source)
                    : null;
        }
        for (TraversalDirection direction : TraversalDirection.values()) {
            if (listed.at().inTheOrderOf(listed.value(), direction, source.newtypes())
                    instanceof PathResolution.At(TermPath at)) {
                return overTheElements(measured.operation(), measured.takenAs(), at, computed,
                        inputs.typeAt(at, source), new RunSource.TraversalOrder(at, direction),
                        inputs, source);
            }
        }
        return null;
    }

    /**
     * What {@code measured} takes over what was computed of each element standing at
     * {@code elements}: the one place that says which number that is, so that one number has one
     * reading however the walk that made it was written.
     *
     * <p>Three numbers are not runs of their own. A total of what is the same number for every
     * element is that number times how many there are — nought where it is nought — as a fold
     * adding it at every step is. What is the element's own place, at the place's own type, is
     * the number taken over that place ({@link #overThePlace}). And what is left is a run over what
     * was computed, in the order the elements were handed where the computation reads it.
     *
     * @param each  what one computed value stands as, with which a place is the place
     * @param order the direction the elements were handed in, where {@code computed} reads where
     *              each stands; null where it does not or nothing showed it
     */
    private static LinearForm<NumericTerm> overTheElements(ValueName.Stdlib operation,
                                                           TakenAs takenAs, TermPath elements,
                                                           ElementValue computed, Type each,
                                                           RunSource.TraversalOrder order,
                                                           InputDomain inputs,
                                                           RuleReadingSource source) {
        if (each == null) {
            return null;
        }
        if (takenAs instanceof TakenAs.TheSumOfWhatItHolds
                && computed instanceof ElementValue.Affine(var alike)
                && alike.coefs().isEmpty()) {
            if (alike.constant().isZero()) {
                return new LinearForm<>(ExactRatio.ZERO, Map.of());
            }
            NumericTerm howMany = howManyStandAt(elements, inputs, source);
            return howMany == null ? null
                    : new LinearForm<>(ExactRatio.ZERO, Map.of(howMany, alike.constant()));
        }
        ElementProjection place = placeStanding(computed, each, elements, inputs, source);
        if (place != null) {
            return atomOf(overThePlace(operation, place.from(elements), inputs, source));
        }
        RunSource over = RunSource.computedOverTheElementsAt(elements, computed, each, order);
        return over == null ? null
                : atomOf(NumericTerm.TakenOver.of(operation, over, each, source.inners(),
                        source.symbols()));
    }

    /**
     * What {@code operation} takes over every occurrence of {@code under}: the taking of the
     * container whose elements those are, where they are one container's elements themselves, and
     * the run over them otherwise — or null where they are no one run.
     *
     * <p>The container's taking and not a run beside it. {@code List.sum(xs)} and a walk answering
     * each element of {@code xs} as it is add up the same values, and two terms for them would be
     * two lines on one number that cancel in no form.
     */
    private static NumericTerm overThePlace(ValueName.Stdlib operation, TermPath under,
                                            InputDomain inputs, RuleReadingSource source) {
        RunSource over = RunSource.overEveryOccurrenceAt(under);
        if (over == null) {
            return null;
        }
        if (over.isInOneContainer()) {
            TermPath container = under.containersHoldingIt().getLast();
            if (under.equals(container.element())) {
                NumericTerm taken = NumericTerm.TakenOf.of(operation,
                        ObservationSource.asItStands(container), TakenArguments.NONE,
                        inputs.typeAt(container, source), source.inners(), source.symbols());
                if (taken != null) {
                    return taken;
                }
            }
        }
        Type stands = inputs.typeAt(under, source);
        return stands == null ? null
                : NumericTerm.TakenOver.of(operation, over, stands, source.inners(),
                        source.symbols());
    }

    /** Whether {@code walk} answers what its closure answered on each element, one for each and
     *  put end to end in the order it was handed them ({@link PieceOfAnElement#THE_CLOSURES_ANSWER}). */
    private static boolean answersInTheOrderHanded(Core walk) {
        AnOperationApplied applied = AnOperationApplied.of(walk);
        BoundOperationFacts.Assembled assembled = applied == null ? null
                : DefaultBoundOperationFacts.get().assembles(applied.operation());
        return assembled != null && assembled.piece() == PieceOfAnElement.THE_CLOSURES_ANSWER;
    }

    /**
     * The elements of {@code list} that a take or drop keeps, as what each element counts for.
     *
     * @param list     the list the elements are kept of
     * @param computed each element counted as itself where its position is kept and as nought
     *                 where it is not
     * @param each     what one computed value stands as
     */
    public record KeptOfAList(Denotation list, ElementValue computed, Type each) {}

    /**
     * What the operation {@code met} keeps of a list by index counts for, where the list is one a
     * dependency answered — or null where it keeps none that way or the count is no whole number
     * written out.
     *
     * <p>The same selection {@link #overTheElementsKeptBy} reads of a list of the input, so that a
     * total of the elements a take keeps is one number whichever list it is of. A count that keeps
     * every element or none is read to the element or to nought, which the caller says what to do
     * with ({@link ElementValue#readsThePosition}).
     */
    public static KeptOfAList keptByIndexOfAnAnswer(Denotation met, RuleReadingSource source) {
        Selection selected = selectionByIndex(met, source);
        if (selected == null) {
            return null;
        }
        Type each = Type.elementOf(Core.withoutStanding(selected.list().value()).type());
        ElementValue computed = keptBy(selected.kept(), new ElementValue.Affine(
                LinearForm.atom(new ElementProjection(List.of()))));
        return each == null ? null : new KeptOfAList(selected.list(), computed, each);
    }

    /** One take or drop: which side of the index it keeps, the index, and the list it is of. */
    private record Cut(Rel kept, long index, Core list) {}

    /**
     * Every take and drop stacked over {@code list}, as the tests an element of {@code list} has
     * to pass to be kept by all of them.
     *
     * @param list the list under all of them, which is not itself a take or drop by a count
     *             written out
     * @param kept the tests of where an element stands in {@code list}: the first position kept,
     *             then the one past the last, each only where it keeps something less than the
     *             whole; and the one test no position passes where nothing is left
     */
    private record Selection(Denotation list, List<ElementValue.PositionTest> kept) {}

    /** The take or drop {@code met} is, or null where it is neither or its count is no whole
     *  number written out. */
    private static Cut cutBy(Denotation met, RuleReadingSource source) {
        AnOperationApplied applied = AnOperationApplied.of(met.value());
        BoundOperationFacts.KeptByIndex byIndex = applied == null ? null
                : DefaultBoundOperationFacts.get().holdsTheElementsByIndex(applied.operation());
        Core count = byIndex == null ? null : applied.argument(byIndex.count());
        Core list = byIndex == null ? null : applied.argument(byIndex.list());
        if (count == null || list == null
                || !(met.at().folded(count, source.symbols(), source.newtypes()).orElse(null)
                        instanceof Long index)) {
            return null;
        }
        return new Cut(byIndex.kept(), index, list);
    }

    /**
     * The takes and drops {@code met} is stacked of, as tests of the position in the list under
     * all of them — or null where it is none.
     *
     * <p>An element is kept by all of them where it passes each, and the position a take or drop
     * tests is its place in the list it is handed. A drop hands on the list from its index, so
     * the positions after it are that many fewer than they stand at in the list under: the index
     * of every selection outside a drop is read that much further on. What is kept comes to the
     * positions from the furthest drop to the nearest take, so however the takes and drops are
     * stacked, the same elements are the same tests. A count below nought keeps the elements as
     * nought does, and the counts that would not sum in a whole number are no selection.
     */
    private static Selection selectionByIndex(Denotation met, RuleReadingSource source) {
        List<Cut> cuts = new ArrayList<>();
        Denotation under = met;
        Cut cut = cutBy(under, source);
        while (cut != null) {
            cuts.add(cut);
            under = under.at().denotes(cut.list(), source.symbols(), source.newtypes());
            cut = cutBy(under, source);
        }
        if (cuts.isEmpty()) {
            return null;
        }
        long from = 0;
        Long before = null;
        for (Cut each : cuts.reversed()) {
            long index = Math.max(each.index(), 0);
            if (index > Long.MAX_VALUE - from) {
                return null;
            }
            if (each.kept() == Rel.GE) {
                from += index;
            } else {
                before = before == null ? from + index : Math.min(before, from + index);
            }
        }
        List<ElementValue.PositionTest> kept = new ArrayList<>();
        if (before != null && before <= from) {
            kept.add(positionTest(Rel.LT, 0));
        } else {
            if (from > 0) {
                kept.add(positionTest(Rel.GE, from));
            }
            if (before != null) {
                kept.add(positionTest(Rel.LT, before));
            }
        }
        return new Selection(under, kept);
    }

    private static ElementValue.PositionTest positionTest(Rel relation, long against) {
        return new ElementValue.PositionTest(ElementValue.PositionTest.THE_POSITION_ITSELF,
                relation, against);
    }

    /** {@code computed} for an element whose position every test of {@code kept} holds of, and
     *  nought for the rest. */
    private static ElementValue keptBy(List<ElementValue.PositionTest> kept,
                                       ElementValue computed) {
        ElementValue chosen = computed;
        for (ElementValue.PositionTest test : kept) {
            chosen = keptBy(test, chosen);
        }
        return chosen;
    }

    /** {@code computed} for an element whose position {@code kept} holds of, and nought for the
     *  rest. */
    private static ElementValue keptBy(ElementValue.PositionTest kept, ElementValue computed) {
        return ElementValue.choosingByPosition(kept, computed,
                new ElementValue.Affine(new LinearForm<>(ExactRatio.ZERO, Map.of())));
    }

    /**
     * The number {@code measured} takes over the values the walk {@code met} was given
     * ({@link #overARun}), or null where those values are not read from a place.
     *
     * @param kept the tests of the position an answer of the walk is counted where, the rest
     *             counting nought; none where every answer counts
     */
    private static LinearForm<NumericTerm> overTheRunWalkedBy(NumericMeasures.Measured measured,
                                                              Denotation met,
                                                              List<ElementValue.PositionTest> kept,
                                                              InputDomain inputs,
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
            case PathResolution.MayStandAt _, PathResolution.MadeOf _ -> null;
        };
        if (at == null) {
            return null;
        }
        // A total of how many a container inside each element holds is how many occurrences of its
        // element there are — where the elements walked are those of a container no other holds.
        // One inside another is one of many, and every occurrence of the path is under every one
        // of them.
        if (kept.isEmpty() && answered == null) {
            ElementProjection counted = countedOfEach(measured, where, element, source);
            if (counted != null && at.containersHoldingIt().size() == 1) {
                return atomOf(howManyStandAt(counted.from(at).element(), inputs, source));
            }
        }
        ElementAnswer closure = where.answerAt(element);
        // The place the answer is, at the place's own type; or what the closure computed, as what
        // the closure answers. Every occurrence of the elements' position, so every occurrence of
        // the place in them: one run where one container holds them, and the lists of an outer list
        // put end to end where several do.
        ElementValue computed;
        Type each;
        if (answered != null) {
            computed = new ElementValue.Affine(LinearForm.atom(answered));
            each = inputs.typeAt(answered.from(at), source);
        } else {
            computed = computedOf(measured, where, element, source,
                    new ElementValue.ElementsAt(at, where.declared()));
            each = closure == null ? null : closure.body().type();
        }
        if (computed == null) {
            return null;
        }
        if (!kept.isEmpty()) {
            computed = keptBy(kept, computed);
            // Some of the answers by where they stand, and an answer stands where its element was
            // handed only where the walk puts them in that order: one answer per element says
            // nothing of which came first. Asked only where what was kept still turns on it.
            if (computed.readsThePosition() && !answersInTheOrderHanded(walk)) {
                return null;
            }
        }
        // A number that turns on where each element stands is a number of them in the order the
        // row writes them, which is asked as well and only then.
        RunSource.TraversalOrder order = computed.readsThePosition()
                ? theOrderTheWalkWasHandedThem(where, element, at, source) : null;
        return overTheElements(measured.operation(), measured.takenAs(), at, computed, each, order,
                inputs, source);
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
        // What the step adds of each element is what a total of it over them is, read where every
        // such total is: a number the same for every element counts them, the element's own place
        // is the taking of that place, and the rest is a run of what was computed.
        LinearForm<NumericTerm> total = overTheElements(SUM,
                DefaultBoundOperationFacts.get().takenAs(SUM), at, step.ofTheElement(),
                walk.step().body().type(), null, inputs, source);
        if (total == null) {
            return null;
        }
        for (Map.Entry<NumericTerm, ExactRatio> each : total.coefs().entrySet()) {
            ExactRatio already = added.get(each.getKey());
            if (already == null) {
                added.put(each.getKey(), each.getValue());
            } else if (already.plus(each.getValue()) instanceof ExactAnswer.Held<ExactRatio>(
                    var both)) {
                added.put(each.getKey(), both);
            } else {
                return null;
            }
        }
        added.values().removeIf(ExactRatio::isZero);
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
     * of them — or null where it is not read.
     *
     * <p>The elements stand at no position of the input, so it is read as the code points of a
     * string are ({@link ElementValue#readWithoutAPlace}). The value may no longer turn on the
     * position: a test of it that holds of every position or of none is read to the element or to
     * nought, and that is what the closure computes.
     */
    public static ElementValue computedOfAnAnswersElement(ElementAnswer closure, InputReads reads,
                                                          RuleReadingSource source) {
        return ElementValue.readWithoutAPlace(closure, reads.heldByTheBody(), source);
    }

    /**
     * What {@code value}, written of the element a walk hands {@code element}, computes of it,
     * where the elements stand at {@code elements} — or null where it is not read.
     *
     * <p>Read as what a closure over the elements answers is ({@link ElementValue#read}), so a
     * field of the element is one way into it and a {@code match} on a place of it is read arm by
     * arm under what the declarations put there. Nothing here says the walk's elements are the
     * ones standing at {@code elements}: that is the caller's to have shown, of every field the
     * value reads.
     *
     * @param reads where {@code value} stands
     */
    public static ElementValue computedOfTheElement(Core value, BindingId element,
                                                    InputReads reads, TermPath elements,
                                                    RuleReadingSource source) {
        return ElementValue.read(new ElementAnswer(element, value, null), reads.heldByTheBody(),
                source, new ElementValue.ElementsAt(elements, reads.declared()));
    }

    /**
     * The same, where {@code value} may add numbers of the input that stand the same for every
     * element beside what it computes of the element ({@link ElementValue#readBeside}) — or null
     * where it is not read.
     *
     * <p>Of the element as {@code walked} says it was made, read through the names the walks on
     * the way hand it by. A number stands the same for every element where it is read in
     * {@code reads} as a position and that position is not at or under where the elements stand:
     * where the walk is, it holds one value, whichever element is being handed.
     *
     * <p>Where the arm making an element is chosen by its case, the number is read of each arm and
     * is the choice by that case ({@link ElementValue.OfItsCase}), so it is chosen as the key read
     * of the same element is ({@link InputReads#keyOf}). What stands beside every element is read
     * only where every arm adds the same of it.
     */
    public static ElementComputation computedOfTheElementBeside(Core value,
                                                                InputReads.WalkedElement walked,
                                                                InputReads reads,
                                                                RuleReadingSource source) {
        TermPath elements = walked.elements();
        List<ElementValue.OfItsCase.Arm> arms = new ArrayList<>();
        LinearForm<NumericTerm> beside = null;
        for (InputReads.WalkedElement.Arm arm : walked.arms()) {
            ElementComputation read = ElementValue.readBeside(
                    new ElementAnswer(walked.element(), value, null), arm.standing(), arm.held(),
                    source, new ElementValue.ElementsAt(elements, reads.declared()),
                    e -> reads.pathOf(e, source.newtypes()) instanceof PathResolution.At(
                            TermPath at) && !at.isAtOrUnder(elements) && !elements.isAtOrUnder(at)
                            ? new NumericTerm.ValueOf(at) : null);
            if (read == null || (beside != null && !beside.equals(read.invariant()))) {
                return null;
            }
            if (walked.subject() == null) {
                return read;
            }
            beside = read.invariant();
            arms.add(new ElementValue.OfItsCase.Arm(arm.cases(), read.relative()));
        }
        return new ElementComputation(
                ElementValue.choosingByCase(walked.subject(), arms, null), beside);
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
     *
     * @param each what one computed value stands as
     */
    private static ElementProjection placeStanding(ElementValue computed, Type each, TermPath at,
                                                   InputDomain inputs, RuleReadingSource source) {
        ElementProjection place = computed.asAPlace();
        if (place == null) {
            return null;
        }
        Type fieldType = inputs.typeAt(place.from(at), source);
        return fieldType != null && TypeOps.base(each, source.inners())
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
