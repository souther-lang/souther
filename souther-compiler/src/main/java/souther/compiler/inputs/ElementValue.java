package souther.compiler.inputs;

import souther.compiler.check.AffineForms;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.ValueStanding;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.ElementAnswer;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.SequencedMap;
import java.util.Set;
import java.util.function.Predicate;

/**
 * What a closure computed from one element of a walk, for a closure whose answer is not a place of
 * the element.
 *
 * <p>The number a walk answers per element when that number is made from the element's fields: an
 * affine form of them, the choice between two such numbers by a flag the element holds, or the
 * choice among them by which case a value of the element is. Relative
 * to the element, so it can be joined to whichever position the run is over, as an
 * {@link ElementProjection} is — and the atoms of a form are those projections, so a field of the
 * element is named the one way wherever it is read.
 *
 * <p><b>The arithmetic is {@link AffineForms}'s.</b> The grammar of what composes a form is the
 * language's, written once; this supplies only what an atom of an element is called. What this
 * adds is the choice, which no form holds: a branch on a flag is one form where the flag is set and
 * another where it is not, an arm of a {@code match} is one form where the value is the case the
 * arm takes, and a single form over the element's fields would have to say which.
 *
 * <p>Not a place. {@link ElementProjection} is where in an element a value stands, and a computed
 * number stands nowhere in it. Held apart so a rule about what a walk computed is never read as a
 * rule about a field.
 *
 * <p>Only what is read exactly. A product of two fields, a call the library does not say the form
 * of, a branch on anything but a flag the element holds, a {@code match} on anything but a place of
 * the element: none is read, and the walk is a run this compiler did not read rather than one it
 * read wrongly.
 */
public sealed interface ElementValue {

    /** The fields of the element this reads, in no order a reader may rely on. */
    Set<ElementProjection> reads();

    /**
     * What this comes to for one element, given the number each field of it holds, which flags
     * are set and which case each value it matches on is; or null where a place it needs is one the
     * element has no number, flag or case at.
     *
     * <p>Asks for a place only where the answer needs it. A choice asks for its flag and then for
     * the fields of the branch the flag picked, and a choice by case asks which case the value is
     * and then for the fields of the arm that took it, so a field only another branch reads is never
     * asked for and whatever the row holds there says nothing about this element. The answers are
     * the caller's to give lazily for that reason.
     *
     * <p>A number the exact arithmetic could not hold is said as that and not as a field that was
     * not there: the first is about this compiler's room and the second about the row.
     */
    ExactAnswer<ExactRatio> at(OneElement element);

    /** What one element holds at the places a computation asks it about. */
    interface OneElement {

        /** The number at {@code field}, or null where the element holds none there. */
        ExactRatio number(ElementProjection field);

        /** Whether the flag at {@code field} is set, or null where the element holds none there. */
        Boolean flag(ElementProjection field);

        /**
         * Which case the value at {@code subject} is, as the test of whether it is one of the cases
         * an arm takes; or null where the element holds nothing there whose case can be told.
         *
         * <p>The value is read once and every arm is tried against it, so a {@code match} of many
         * arms reads its subject once per element and not once per arm.
         */
        Predicate<CasesLeft> caseAt(ElementProjection subject);
    }

    /**
     * The field this is, where it is that field and nothing made of it, or null.
     *
     * <p>A number made of the element by weighing one field once and adding nothing is the field.
     * Such a computation is the place and is read as the place, so that one number is not two
     * terms by the way its closure happened to be spelled.
     */
    ElementProjection asAPlace();

    /**
     * What {@code one} and the form {@code other} come to added, for each element; or null where
     * the exact arithmetic cannot hold a number of it.
     *
     * <p>A form added to a choice is added to each of its answers,
     * {@code 1 + case(A ↦ a, B ↦ b) = case(A ↦ 1 + a, B ↦ 1 + b)}, and an element takes the same arm
     * either way. That is as large as the choice is, once over, so a choice with a form beside it
     * is that choice and is solved for, bounded and read through its arms like any other.
     *
     * <p>A form and never a second choice. Two choices pushed into each other are every pair of
     * their answers, and choices independent of one another, added up, would come to as many
     * answers as the product of theirs — a sum written in a line held as a tree doubling at each
     * term. Choices are added by being held side by side ({@link SumOfChoices}), and the type of
     * {@code other} is what keeps a product of them from being made anywhere.
     */
    static ElementValue plus(ElementValue one, Affine other) {
        return switch (one) {
            case Affine form -> form.form().plus(other.form())
                    instanceof ExactAnswer.Held<LinearForm<ElementProjection>>(var summed)
                    ? new Affine(summed) : null;
            case Choose choice -> {
                ElementValue yes = plus(choice.whenSet(), other);
                ElementValue no = yes == null ? null : plus(choice.otherwise(), other);
                yield no == null ? null : choosing(choice.flag(), yes, no);
            }
            case OfItsCase choice -> {
                List<OfItsCase.Arm> arms = new ArrayList<>();
                for (OfItsCase.Arm arm : choice.arms()) {
                    ElementValue added = plus(arm.value(), other);
                    if (added == null) {
                        yield null;
                    }
                    arms.add(new OfItsCase.Arm(arm.cases(), added));
                }
                ElementValue rest = choice.rest() == null ? null : plus(choice.rest(), other);
                yield choice.rest() != null && rest == null ? null
                        : choosingByCase(choice.subject(), arms, rest);
            }
            case SumOfChoices sum -> plus(sum.besides(), other) instanceof Affine besides
                    ? new SumOfChoices(besides, sum.chosen()) : null;
        };
    }

    /** What {@code value} comes to weighed by {@code weight}, for each element, pushed into every
     *  answer of a choice as {@link #plus} is; or null where the exact arithmetic cannot hold it. */
    static ElementValue times(ElementValue value, ExactRatio weight) {
        return switch (value) {
            case Affine form -> form.form().times(weight)
                    instanceof ExactAnswer.Held<LinearForm<ElementProjection>>(var weighed)
                    ? new Affine(weighed) : null;
            case Choose choice -> {
                ElementValue yes = times(choice.whenSet(), weight);
                ElementValue no = yes == null ? null : times(choice.otherwise(), weight);
                yield no == null ? null : choosing(choice.flag(), yes, no);
            }
            case OfItsCase choice -> {
                List<OfItsCase.Arm> arms = new ArrayList<>();
                for (OfItsCase.Arm arm : choice.arms()) {
                    ElementValue weighed = times(arm.value(), weight);
                    if (weighed == null) {
                        yield null;
                    }
                    arms.add(new OfItsCase.Arm(arm.cases(), weighed));
                }
                ElementValue rest = choice.rest() == null ? null : times(choice.rest(), weight);
                yield choice.rest() != null && rest == null ? null
                        : choosingByCase(choice.subject(), arms, rest);
            }
            case SumOfChoices sum -> {
                if (weight.isZero()) {
                    yield new Affine(LinearForm.constant(ExactRatio.ZERO));
                }
                if (!(times(sum.besides(), weight) instanceof Affine besides)) {
                    yield null;
                }
                SequencedMap<ElementValue, ExactRatio> chosen = new LinkedHashMap<>();
                for (Map.Entry<ElementValue, ExactRatio> each : sum.chosen().entrySet()) {
                    if (!(each.getValue().times(weight)
                            instanceof ExactAnswer.Held<ExactRatio>(var weighed))) {
                        yield null;
                    }
                    chosen.put(each.getKey(), weighed);
                }
                yield new SumOfChoices(besides, chosen);
            }
        };
    }

    /**
     * Choices of the element held side by side and added up, each at its weight, and a form beside
     * them: {@code besides + Σ weight·choice}.
     *
     * <p>Each choice is made for the element on its own, so the sum is as large as its choices
     * together and not as the number of ways they can fall out together. Two or more, and each a
     * choice ({@link Choose}, {@link OfItsCase}): one choice takes the form into its answers
     * ({@link #plus}), and a form is no choice.
     *
     * <p>One value however its terms were written. The choices are a mapping, so two of these are
     * equal and hash alike by which choices they add at which weights and by nothing else; and the
     * mapping is laid out once, where one of these is made, in an order made of the choices alone,
     * which every reader then takes them in — what an element comes to, where a row first has
     * nothing, and how the sum is spelled.
     *
     * @param chosen each choice, at the weight it is added at, never nought
     */
    record SumOfChoices(Affine besides, SequencedMap<ElementValue, ExactRatio> chosen)
            implements ElementValue {

        public SumOfChoices {
            if (besides == null || chosen == null || chosen.size() < 2) {
                throw new IllegalArgumentException("a sum of choices holds a form and choices to"
                        + " add to it");
            }
            for (Map.Entry<ElementValue, ExactRatio> each : chosen.entrySet()) {
                if (!(each.getKey() instanceof Choose || each.getKey() instanceof OfItsCase)
                        || each.getValue().isZero()) {
                    throw new IllegalArgumentException("what a sum of choices adds is choices,"
                            + " each weighed by something, and this is " + each);
                }
            }
            chosen = laidOut(chosen);
        }

        /** {@code chosen} in the one order the choices' spelling gives, and fixed. */
        private static SequencedMap<ElementValue, ExactRatio> laidOut(
                Map<ElementValue, ExactRatio> chosen) {
            List<Map.Entry<ElementValue, ExactRatio>> inOrder = new ArrayList<>(chosen.entrySet());
            inOrder.sort(Comparator.comparing(each -> each.getKey().toString()));
            SequencedMap<ElementValue, ExactRatio> out = new LinkedHashMap<>();
            inOrder.forEach(each -> out.put(each.getKey(), each.getValue()));
            return Collections.unmodifiableSequencedMap(out);
        }

        @Override
        public Set<ElementProjection> reads() {
            Set<ElementProjection> all = new LinkedHashSet<>(besides.reads());
            chosen.keySet().forEach(each -> all.addAll(each.reads()));
            return Set.copyOf(all);
        }

        /** Every choice is made for the element, and each asks only for what its own answer
         *  needs. */
        @Override
        public ExactAnswer<ExactRatio> at(OneElement element) {
            ExactAnswer<ExactRatio> total = besides.at(element);
            for (Map.Entry<ElementValue, ExactRatio> each : chosen.entrySet()) {
                if (total == null) {
                    return null;
                }
                ExactAnswer<ExactRatio> one = each.getKey().at(element);
                if (one == null) {
                    return null;
                }
                total = total.flatMap(sofar -> one.flatMap(made ->
                        made.times(each.getValue()).flatMap(sofar::plus)));
            }
            return total;
        }

        /** A sum is made of the element and is not a field of it. */
        @Override
        public ElementProjection asAPlace() {
            return null;
        }

        @Override
        public String toString() {
            List<String> terms = new ArrayList<>();
            chosen.forEach((choice, weight) -> terms.add(weight + "·(" + choice + ")"));
            terms.add(besides.toString());
            return String.join(" + ", terms);
        }
    }

    /**
     * {@code constant + Σ weight·place + Σ weight·choice}, each of {@code chosen} a choice
     * ({@link Choose}, {@link OfItsCase}) met once; or null where the exact arithmetic cannot hold
     * it.
     *
     * <p>Without a choice it is a form; with one, that choice with the form in its answers; with
     * more, the choices held side by side ({@link SumOfChoices}).
     */
    static ElementValue summed(ExactRatio constant, Map<ElementProjection, ExactRatio> places,
                               Map<ElementValue, ExactRatio> chosen) {
        Affine besides = new Affine(new LinearForm<>(constant, places));
        if (chosen.isEmpty()) {
            return besides;
        }
        if (chosen.size() == 1) {
            Map.Entry<ElementValue, ExactRatio> only = chosen.entrySet().iterator().next();
            ElementValue weighed = times(only.getKey(), only.getValue());
            return weighed == null ? null : plus(weighed, besides);
        }
        return new SumOfChoices(besides, new LinkedHashMap<>(chosen));
    }

    /**
     * The choice of {@code whenSet} or {@code otherwise} by {@code flag}, with a choice between
     * two answers that are one answer being that answer.
     *
     * <p>The one way a choice is made, so that what a choice comes to is not two values by whether
     * its flag was asked about. A flag the answer does not turn on is no field the number reads.
     */
    static ElementValue choosing(ElementProjection flag, ElementValue whenSet,
                                 ElementValue otherwise) {
        return whenSet.equals(otherwise) ? whenSet : new Choose(flag, whenSet, otherwise);
    }

    /** {@code const + Σ coef·field}. */
    record Affine(LinearForm<ElementProjection> form) implements ElementValue {

        public Affine {
            if (form == null) {
                throw new IllegalArgumentException("a number made of the element is a form of it");
            }
        }

        @Override
        public Set<ElementProjection> reads() {
            return Set.copyOf(form.coefs().keySet());
        }

        @Override
        public ExactAnswer<ExactRatio> at(OneElement element) {
            ExactAnswer<ExactRatio> total = ExactAnswer.held(form.constant());
            for (Map.Entry<ElementProjection, ExactRatio> each : form.coefs().entrySet()) {
                ExactRatio held = element.number(each.getKey());
                if (held == null) {
                    return null;
                }
                total = total.flatMap(
                        sofar -> each.getValue().times(held).flatMap(sofar::plus));
            }
            return total;
        }

        @Override
        public ElementProjection asAPlace() {
            if (!form.constant().isZero() || form.coefs().size() != 1) {
                return null;
            }
            Map.Entry<ElementProjection, ExactRatio> only =
                    form.coefs().entrySet().iterator().next();
            return only.getValue().equals(ExactRatio.ONE) ? only.getKey() : null;
        }

        @Override
        public String toString() {
            List<String> terms = new ArrayList<>();
            form.coefs().entrySet().stream()
                    .sorted(Map.Entry.comparingByKey(
                            Comparator.comparing(ElementProjection::toString)))
                    .forEach(each -> terms.add(each.getValue() + "·" + each.getKey()));
            terms.add(form.constant().toString());
            return String.join(" + ", terms);
        }
    }

    /** {@code whenSet} where the element's flag {@code flag} is set, and {@code otherwise} where it
     *  is not. */
    record Choose(ElementProjection flag, ElementValue whenSet, ElementValue otherwise)
            implements ElementValue {

        public Choose {
            if (flag == null || whenSet == null || otherwise == null) {
                throw new IllegalArgumentException("a choice is of a flag and both of its answers");
            }
        }

        @Override
        public Set<ElementProjection> reads() {
            Set<ElementProjection> all = new LinkedHashSet<>();
            all.add(flag);
            all.addAll(whenSet.reads());
            all.addAll(otherwise.reads());
            return Set.copyOf(all);
        }

        @Override
        public ExactAnswer<ExactRatio> at(OneElement element) {
            Boolean set = element.flag(flag);
            return set == null ? null : (set ? whenSet : otherwise).at(element);
        }

        /** A choice is made of the element and is not a field of it. */
        @Override
        public ElementProjection asAPlace() {
            return null;
        }

        @Override
        public String toString() {
            return "if " + flag + " then " + whenSet + " else " + otherwise;
        }
    }

    /**
     * The value of the first arm that takes the case the value at a place of the element is, the
     * arms tried in the order the {@code match} wrote them; and {@code rest} where none of them
     * takes it.
     *
     * <p>Chosen for each element on its own. Which arm an element is taken by is a fact about that
     * element, and a total over the run is the total of what each one's arm made of it — so one
     * container stays one run, and no arm is a run of its own.
     *
     * <p>Each arm's name stands at the matched value narrowed to what the arm took ({@link #taken}).
     * What a body under the arm reads of that value is a field of the case, and two cases declaring
     * a field of one name are two places.
     *
     * @param subject the place whose case chooses, which every arm narrows
     * @param rest    what an element no arm took comes to, or null where the arms take every value
     *                the declaration leaves the place
     */
    record OfItsCase(ElementProjection subject, List<Arm> arms, ElementValue rest)
            implements ElementValue {

        /** An arm: the cases it takes that no arm before it took, and what it comes to there. */
        public record Arm(CasesLeft cases, ElementValue value) {

            public Arm {
                if (cases == null || value == null) {
                    throw new IllegalArgumentException("an arm takes some case and answers"
                            + " something of it");
                }
            }
        }

        public OfItsCase {
            if (subject == null || arms == null || arms.isEmpty()) {
                throw new IllegalArgumentException("a choice by case has a place and an arm to"
                        + " choose");
            }
            arms = List.copyOf(arms);
        }

        /** Where the name of {@code arm} stands: the subject, narrowed to what the arm took. */
        public ElementProjection taken(Arm arm) {
            return subject.narrowedTo(arm.cases());
        }

        @Override
        public Set<ElementProjection> reads() {
            Set<ElementProjection> all = new LinkedHashSet<>();
            all.add(subject);
            for (Arm arm : arms) {
                all.addAll(arm.value().reads());
            }
            if (rest != null) {
                all.addAll(rest.reads());
            }
            return Set.copyOf(all);
        }

        @Override
        public ExactAnswer<ExactRatio> at(OneElement element) {
            Predicate<CasesLeft> isOf = element.caseAt(subject);
            if (isOf == null) {
                return null;
            }
            for (Arm arm : arms) {
                if (isOf.test(arm.cases())) {
                    return arm.value().at(element);
                }
            }
            return rest == null ? null : rest.at(element);
        }

        /** A choice is made of the element and is not a field of it. */
        @Override
        public ElementProjection asAPlace() {
            return null;
        }

        @Override
        public String toString() {
            List<String> said = new ArrayList<>();
            for (Arm arm : arms) {
                said.add("when " + taken(arm) + " then " + arm.value());
            }
            if (rest != null) {
                said.add("otherwise " + rest);
            }
            return String.join(" ", said);
        }
    }

    /**
     * The choice by case of {@code arms} and {@code rest}, with a choice whose every answer is one
     * answer being that answer.
     *
     * <p>A {@code match} is exhaustive, so an element is taken by some arm, and where every arm
     * comes to the same thing the case does not change what the element comes to.
     */
    static ElementValue choosingByCase(ElementProjection subject, List<OfItsCase.Arm> arms,
                                       ElementValue rest) {
        if (arms.isEmpty()) {
            return rest;
        }
        ElementValue first = arms.getFirst().value();
        boolean one = rest == null || rest.equals(first);
        for (OfItsCase.Arm arm : arms) {
            one &= arm.value().equals(first);
        }
        return one ? first : new OfItsCase(subject, arms, rest);
    }

    /**
     * What a licensed closure computed of its element, or null where that is not read.
     *
     * <p>Asked after {@link ElementProjection#read} has answered null: an answer that is a place of
     * the element is a place and is not made into a one-field form. Wherever the closure's answer is
     * arithmetic over fields, a name bound to either, a branch on a flag between two of them, or a
     * {@code match} on a place of the element whose arms are each of these, this says which.
     *
     * @param held what each binding of the body holds, so that a name on the way is read through
     * @param elements where the elements the closure is handed stand, which is what says whether
     *                 an arm of a {@code match} on one narrows it
     */
    static ElementValue read(ElementAnswer answer, Map<BindingId, Core> held,
                             RuleReadingSource source, ElementsAt elements) {
        return new Reader(answer.parameter(), Map.of(), held, source, elements)
                .value(answer.body());
    }

    /**
     * Where the elements of a walk stand, and what the declarations put there.
     *
     * <p>What an arm of a {@code match} on an element takes is the declaration's to say at that
     * position ({@link DeclaredInput#taking}): it narrows the value, finds it already the case, or
     * finds no value there of it. Asked of the closure alone, an arm would narrow a position to a
     * case it already is, and the place it named would be one the reading of the input spells
     * another way.
     */
    record ElementsAt(TermPath at, DeclaredInput declared) {

        public ElementsAt {
            if (at == null || declared == null) {
                throw new IllegalArgumentException("the elements stand somewhere declared");
            }
        }
    }

    /** One reading of one closure's answer. */
    final class Reader {

        private final BindingId element;
        /** Where in the element each name an arm on the way bound stands. */
        private final Map<BindingId, ElementProjection> standing;
        private final Map<BindingId, Core> held;
        private final RuleReadingSource source;
        private final ElementsAt elements;

        private Reader(BindingId element, Map<BindingId, ElementProjection> standing,
                       Map<BindingId, Core> held, RuleReadingSource source, ElementsAt elements) {
            this.element = element;
            this.standing = standing;
            this.held = held;
            this.source = source;
            this.elements = elements;
        }

        /** The same reading, inside an arm whose name {@code bound} stands at {@code at}. */
        private Reader binding(Core.Binder bound, ElementProjection at) {
            if (bound == null || bound.binding() == null) {
                return this;
            }
            Map<BindingId, ElementProjection> wider = new LinkedHashMap<>(standing);
            wider.put(bound.binding(), at);
            return new Reader(element, Map.copyOf(wider), held, source, elements);
        }

        private ElementProjection placeOf(Core e, Map<BindingId, Core> at) {
            return ElementProjection.read(e, element, standing, at, source.newtypes());
        }

        /**
         * What {@code answer} comes to of the element: a form of its places and of the choices in
         * it, put together as {@link #summed} puts them.
         *
         * <p>One walk, the arithmetic's own. A choice is no arithmetic, so the walk stops at one and
         * asks what it is as it asks of any place it cannot compose ({@link #atoms}); a name given
         * a choice is read through to it by the same walk as a name given arithmetic. So a choice
         * is read the same way as the whole answer, as a part of a sum, or behind a name.
         */
        private ElementValue value(Core answer) {
            LinearForm<Atom> form = AffineForms.of(answer, held, atoms());
            if (form == null) {
                return null;
            }
            Map<ElementProjection, ExactRatio> places = new LinkedHashMap<>();
            Map<ElementValue, ExactRatio> chosen = new LinkedHashMap<>();
            form.coefs().forEach((atom, weight) -> {
                switch (atom) {
                    case Atom.Place(ElementProjection place) -> places.put(place, weight);
                    case Atom.Chosen(ElementValue choice) -> chosen.put(choice, weight);
                }
            });
            return ElementValue.summed(form.constant(), places, chosen);
        }

        /** What an atom of what a closure computed is: a place of the element, or a choice made
         *  of it. */
        private sealed interface Atom {

            record Place(ElementProjection place) implements Atom {}

            record Chosen(ElementValue choice) implements Atom {}
        }

        /** What a branch on a flag of the element comes to, or null where it is not read. */
        private ElementValue byFlag(Core.If branch) {
            ElementProjection flag = placeOf(branch.cond(), held);
            ElementValue yes = flag == null ? null : value(branch.then());
            ElementValue no = yes == null ? null : value(branch.els());
            return no == null ? null : ElementValue.choosing(flag, yes, no);
        }

        /**
         * What a {@code match} on a place of the element comes to: each arm read with its name
         * standing at the place the arm narrowed, or null where any arm is not read.
         *
         * <p>Which of the arms a value can reach is the declaration's to say at the place the
         * elements stand. An arm no value there is of is no arm any element takes, and is left out;
         * one every value left there is of takes all of them, and the arms after it are not reached.
         * An arm selecting nothing — the one written to take whatever is left — does the same.
         *
         * <p>Each arm is asked about the whole declaration and not about what the arms before it
         * left, because no two arms of a {@code match} select one case: the checker refuses that
         * (E1204), so what an arm selects is what it takes.
         */
        private ElementValue byCase(Core.Match match) {
            ElementProjection subject = placeOf(match.scrutinee(), held);
            if (subject == null) {
                return null;
            }
            TermPath at = subject.from(elements.at());
            List<OfItsCase.Arm> arms = new ArrayList<>();
            // What the arms narrow, which is the subject or, where it was narrowed to several
            // cases already, the place that narrowing was of.
            ElementProjection narrowed = null;
            for (Core.Case arm : match.cases()) {
                CasesLeft covered = arm.pattern() == null ? null
                        : CasesLeft.selectedBy(arm.pattern());
                if (arm.pattern() != null && covered == null) {
                    return null;
                }
                DeclaredInput.Taking taking = covered == null ? new DeclaredInput.Taking.Implied()
                        : elements.declared().taking(at, match.scrutinee().type(), covered);
                switch (taking) {
                    case DeclaredInput.Taking.Excluded _ -> { }
                    case DeclaredInput.Taking.Implied _ -> {
                        ElementValue rest = binding(arm.binder(), subject).value(arm.body());
                        return rest == null ? null
                                : ElementValue.choosingByCase(narrowed, arms, rest);
                    }
                    case DeclaredInput.Taking.Narrows(TermPath to) -> {
                        // What an arm takes is the place the elements stand at narrowed, below
                        // them; and every arm of one match narrows the one place, since a
                        // narrowing to several cases is narrowed again in place by each of them.
                        ElementProjection reached = ElementProjection.below(elements.at(), to);
                        if (reached == null || reached.narrowing() == null
                                || (narrowed != null
                                        && !narrowed.equals(reached.narrowedFrom()))) {
                            throw new IllegalStateException("an arm of a match on " + subject
                                    + " was taken at " + to + ", which narrows no place the other"
                                    + " arms narrow below " + elements.at());
                        }
                        ElementValue value = binding(arm.binder(), reached).value(arm.body());
                        if (value == null) {
                            return null;
                        }
                        narrowed = reached.narrowedFrom();
                        arms.add(new OfItsCase.Arm(reached.narrowing(), value));
                    }
                }
            }
            return arms.isEmpty() ? null : ElementValue.choosingByCase(narrowed, arms, null);
        }

        /**
         * What an atom of an element is called: the way to it from the element, and what a name on
         * the way holds; or, where the walk stopped at a branch on a flag of the element or a
         * {@code match} on a place of it, that choice.
         */
        private AffineForms.Reading<Atom, Map<BindingId, Core>> atoms() {
            return new Names<>() {

                @Override
                public LinearForm<Atom> leafOf(Core e, Map<BindingId, Core> at) {
                    ElementProjection place = placeOf(e, at);
                    if (place != null) {
                        return LinearForm.atom(new Atom.Place(place));
                    }
                    ElementValue choice = switch (Core.withoutStanding(e)) {
                        case Core.If branch -> byFlag(branch);
                        case Core.Match match -> byCase(match);
                        case null, default -> null;
                    };
                    return choice == null ? null : termsOf(choice);
                }
            };
        }

        /**
         * {@code value} as terms of a form: a form is its own places, a sum of choices its form
         * and each of its choices, and a choice one term.
         *
         * <p>What a branch or a {@code match} came to need not be a choice — two answers that are
         * one are that answer, and arms adding choices up are a sum of them — and is put into the
         * form as what it is, so that the form a choice stands in is made the one way however the
         * choice turned out.
         */
        private static LinearForm<Atom> termsOf(ElementValue value) {
            return switch (value) {
                case Affine form -> {
                    Map<Atom, ExactRatio> places = new LinkedHashMap<>();
                    form.form().coefs().forEach((place, weight) ->
                            places.put(new Atom.Place(place), weight));
                    yield new LinearForm<>(form.form().constant(), places);
                }
                case SumOfChoices sum -> {
                    LinearForm<Atom> besides = termsOf(sum.besides());
                    Map<Atom, ExactRatio> all = new LinkedHashMap<>(besides.coefs());
                    sum.chosen().forEach((choice, weight) ->
                            all.put(new Atom.Chosen(choice), weight));
                    yield new LinearForm<>(besides.constant(), all);
                }
                case Choose _, OfItsCase _ -> LinearForm.atom(new Atom.Chosen(value));
            };
        }

        /**
         * What a closure answers of one element and of the answer so far, as a form of both, and
         * what it adds to the answer so far where it is that answer and something of the element
         * alone.
         *
         * <p>The answer so far is an atom of the form like any field of the element, and the step
         * is that form only where the arithmetic composes it. So the step is shown to be
         * {@code 1·answer + w(element)} for every answer there is, where a step read at two answers
         * and found to agree there would be shown it for those two: {@code answer * answer + x} is
         * {@code x} at nought and {@code 1 + x} at one, and is no addition at two.
         *
         * <p>Null where the form has the answer so far at any weight but exactly one — which is
         * where it is multiplied, ignored or chosen between. What every element adds alike is the
         * constant, and a step adding nothing else of the element adds that many for each of them.
         *
         * <p>A choice of the element the step adds is read as it is in a closure's answer
         * ({@link #value}): {@code acc + (if a.debit then a.q else 0)} adds the choice. A choice
         * holding the answer so far is no choice of the element, and is not read.
         */
        private Added addedTo(Core answer, BindingId accumulator) {
            LinearForm<TheStep> form = AffineForms.of(answer, held, new Names<TheStep>() {

                @Override
                public LinearForm<TheStep> leafOf(Core e, Map<BindingId, Core> at) {
                    if (Core.withoutStanding(e) instanceof Core.Read read
                            && read.binding().equals(accumulator)) {
                        return LinearForm.atom(new TheStep.TheAnswerSoFar());
                    }
                    ElementProjection counted = countedAt(e, element, at, source);
                    if (counted != null) {
                        return LinearForm.atom(new TheStep.HowManyAt(counted));
                    }
                    LinearForm<Atom> ofTheElement = atoms().leafOf(e, at);
                    if (ofTheElement == null) {
                        return null;
                    }
                    Map<TheStep, ExactRatio> terms = new LinkedHashMap<>();
                    ofTheElement.coefs().forEach((atom, weight) ->
                            terms.put(new TheStep.OfTheElement(atom), weight));
                    return new LinearForm<>(ofTheElement.constant(), terms);
                }
            });
            if (form == null
                    || !ExactRatio.ONE.equals(form.coefs().get(new TheStep.TheAnswerSoFar()))) {
                return null;
            }
            Map<ElementProjection, ExactRatio> places = new LinkedHashMap<>();
            Map<ElementValue, ExactRatio> chosen = new LinkedHashMap<>();
            Map<ElementProjection, ExactRatio> counted = new LinkedHashMap<>();
            form.coefs().forEach((atom, weight) -> {
                switch (atom) {
                    case TheStep.OfTheElement(Atom.Place(ElementProjection place)) ->
                            places.put(place, weight);
                    case TheStep.OfTheElement(Atom.Chosen(ElementValue choice)) ->
                            chosen.put(choice, weight);
                    case TheStep.HowManyAt(ElementProjection place) -> counted.put(place, weight);
                    case TheStep.TheAnswerSoFar _ -> { }
                }
            });
            ElementValue adds = ElementValue.summed(form.constant(), places, chosen);
            return adds == null ? null : new Added(adds, counted);
        }

        /** What an atom of a step is: the answer so far, an atom of the element, or how many the
         *  container at a place of the element holds. */
        private sealed interface TheStep {

            record TheAnswerSoFar() implements TheStep {}

            record OfTheElement(Atom atom) implements TheStep {}

            record HowManyAt(ElementProjection place) implements TheStep {}
        }

        /**
         * How a closure's body is read through the names it holds, whatever its atoms are: a name
         * is what the body bound it to, and the element is no name that holds anything.
         *
         * @param <A> what an atom is called
         */
        private abstract class Names<A> implements AffineForms.Reading<A, Map<BindingId, Core>> {

            @Override
            public Symbols symbols() {
                return source.symbols();
            }

            @Override
            public DeclarationAccess declarations() {
                return source.declarations();
            }

            @Override
            public Map<BindingId, Core> inside(Core.LetIn li, Map<BindingId, Core> at) {
                return at;
            }

            @Override
            public ValueStanding.ReadThrough<Map<BindingId, Core>> readThrough(
                    Core.Read read, Map<BindingId, Core> at) {
                Core value = element.equals(read.binding()) ? null : at.get(read.binding());
                return value == null ? null : new ValueStanding.ReadThrough<>(value, at);
            }

            @Override
            public List<ValueStanding.ReadThrough<Map<BindingId, Core>>> alternativesOf(
                    Core.Read read, Map<BindingId, Core> at) {
                return null;
            }

            @Override
            public boolean readsThrough(Core.FieldAccess fa, Map<BindingId, Core> at) {
                return false;
            }
        }
    }

    /**
     * What a step adds to the answer so far for one element: what it computes of the element's
     * numbers, and how many each container at a place of the element holds, with the weight it is
     * added at.
     *
     * <p>A count is no number of the element's: how many a list inside it holds is as many values
     * as stand inside, so over every element it is how many occurrences of that list's element
     * there are, which is a number of the walk and not a total of one value of each element.
     */
    record Added(ElementValue ofTheElement, Map<ElementProjection, ExactRatio> heldAt) {

        public Added {
            heldAt = Map.copyOf(heldAt);
        }
    }

    /**
     * What a step answering the answer so far and something of the element adds to it, or null
     * where it adds anything but that ({@link Reader#addedTo}).
     *
     * @param accumulator the parameter the answer so far arrives on
     */
    static Added addedTo(ElementAnswer step, BindingId accumulator, Map<BindingId, Core> held,
                         RuleReadingSource source, ElementsAt elements) {
        return new Reader(step.parameter(), Map.of(), held, source, elements)
                .addedTo(step.body(), accumulator);
    }

    /**
     * The place of the element {@code e} counts what the container there holds of, where it is
     * how many that container holds taken as it stands — or null where it is anything else.
     */
    static ElementProjection countedAt(Core e, BindingId element, Map<BindingId, Core> held,
                                       RuleReadingSource source) {
        NumericMeasures.Measured measured = NumericMeasures.takenIn(e, source.symbols(),
                _ -> Optional.empty());
        return measured != null && measured.arguments().none()
                && DefaultBoundOperationFacts.get().takenAs(measured.operation())
                        instanceof TakenAs.HowManyItHolds
                ? ElementProjection.read(measured.of(), element, held, source.newtypes()) : null;
    }
}
