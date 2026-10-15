package souther.compiler.semantics;

import java.util.List;
import java.util.function.Function;

/**
 * Where an element of what an operation answers came from, said the way it runs.
 *
 * <p>Consumer-neutral, and that is the whole of why it exists. Two checks want this and want
 * opposite halves of it: the invariant discharge reads it forwards — what was stated of a source
 * still holds of what was built from it — and a reading of coverage reads it backwards, from a value
 * in the answer to the input position it came from. Written for either one, it comes out as that
 * one's projection, and the other is left recovering what the projection dropped.
 *
 * <p>Which is what {@link ElementShape} is. It is a good answer to the discharge question
 * and a lossy one to any other: {@code List.filterMap} and {@code Set.map} are both
 * {@code COLLAPSES}, because for discharge it is enough that neither keeps what was stated and
 * neither grows — and their elements do not come from the same place at all. One is what the closure
 * answered, and the other is inside what the closure answered. So the shape is derived from this
 * ({@link BuiltFrom#shape}) and this is not derived from the shape.
 *
 * <p><b>Provenance and nothing else.</b> Saying an element came from a closure applied to an input
 * element does not say a value can be chosen at the input that puts the result where a rule wants
 * it: a closure is any total function, and {@code x -> x + 1} is invertible where
 * {@code x -> f(x)} in general is not. Whether a constraint can be pushed back to a row is a
 * separate question asked of a separate answer, and a reader that took this for one would have
 * "the origin is known, so the value can be built" — which is true of nothing here.
 *
 * <p><b>And no count.</b> How many elements the result has is {@link SizeAgainstItsSource} and
 * is stated beside this. They are different algebras and they come apart: {@code List.map} and
 * {@code Set.map} have one lineage — the closure's answer on an element of the source — and
 * different counts, because two elements of a set may map onto one. Folded together, the count would
 * decide the provenance.
 *
 * <p><b>Generic in the word for an argument</b>, as {@link souther.compiler.numeric.LinearForm} is.
 * A lineage names the argument its elements come from, and what that name is depends on which side
 * of the binding it stands: authored, it is an {@link ArgumentRef}, the word a fact is written in;
 * held to the library, it is the declaration's own argument. The structure between the two is one
 * structure, so it is written once and the word is a parameter.
 *
 * @param <A> the word for an argument of the operation
 */
public sealed interface ElementLineage<A> {

    /**
     * Where in what an operation answers the elements this is about stand.
     *
     * <p>An operation answers one value and that value may hold more than one run of elements.
     * {@code List.partition} answers two lists and each holds elements of the input;
     * {@code List.zipShortest} answers one list whose elements are pairs, and the two halves of a
     * pair come from different arguments. Neither is a lineage with something extra on it — they are
     * two lineages, at two places in one answer — so what an operation declares is a lineage per
     * place and not a lineage.
     *
     * @param steps from the answer inwards
     */
    record ResultPath(List<Step> steps) {

        public ResultPath {
            steps = List.copyOf(steps);
        }

        /** One step into what an operation answers. */
        public sealed interface Step {

            /** Inside the sequence reached so far. */
            record Element() implements Step {

                @Override
                public String toString() {
                    return "[*]";
                }
            }

            /** One component of a tuple. */
            record Component(int index) implements Step {

                @Override
                public String toString() {
                    return "." + index;
                }
            }
        }

        /** The elements of what the operation answers, which is where most of them are. */
        public static ResultPath elements() {
            return new ResultPath(List.of(new Step.Element()));
        }

        public ResultPath then(Step step) {
            List<Step> longer = new java.util.ArrayList<>(steps);
            longer.add(step);
            return new ResultPath(longer);
        }

        @Override
        public String toString() {
            StringBuilder out = new StringBuilder("result");
            steps.forEach(out::append);
            return out.toString();
        }
    }

    /** One run of elements in what an operation answers, and where they came from. */
    record OutputLineage<A>(ResultPath at, ElementLineage<A> origin) {}

    /**
     * How far inside an argument the elements come from.
     *
     * @param argument which argument, as every rule here names one
     * @param elements how many sequence-element traversals inside it — one for the elements of a
     *                 container, two for the elements of what a container of containers holds,
     *                 which is what {@code List.concat} draws from. A count of that one traversal
     *                 and not a depth: what an optional holds and what a map holds are steps of
     *                 their own and are not this, so a lineage into either wants a path here rather
     *                 than a larger number
     */
    record Source<A>(A argument, int elements) {

        public Source {
            java.util.Objects.requireNonNull(argument, "a lineage names the argument it is from");
            if (elements < 1) {
                throw new IllegalArgumentException(
                        "a lineage is about the elements of something: " + elements);
            }
        }

        /** The same source with its argument read as {@code word} reads it. */
        public <B> Source<B> withArgument(Function<A, B> word) {
            return new Source<>(word.apply(argument), elements);
        }
    }

    /** Where the elements this is about come from, or null where they come from more than one
     *  place. */
    Source<A> source();

    /**
     * The same lineage with every argument it names read as {@code word} reads it.
     *
     * <p>Structure and nothing else: which arguments there are, and where each stands in the
     * lineage, are what this keeps, and what an argument becomes is the caller's. This is how a
     * lineage crosses from the vocabulary a fact is authored in to the one a reader is handed,
     * without the reader rebuilding the shape.
     */
    default <B> ElementLineage<B> withArguments(Function<A, B> word) {
        return switch (this) {
            case SameAs<A> same -> new SameAs<>(same.source().withArgument(word));
            case ClosureResult<A> made -> new ClosureResult<>(made.source().withArgument(word));
            case InsideClosureResult<A> inside ->
                    new InsideClosureResult<>(inside.source().withArgument(word));
            case TupleComponent<A> part ->
                    new TupleComponent<>(part.source().withArgument(word), part.index(),
                            part.filedUnder());
            case OneOf<A> one -> new OneOf<>(one.alternatives().stream()
                    .map(each -> each.withArguments(word)).toList());
        };
    }

    /**
     * The value at the output position is the value at the source position.
     *
     * <p>An identity between two positions, and not a statement that the operation keeps its
     * container's elements. Read the second way, {@code List.concat} would not be one — its answer
     * is not its argument's elements, it is the elements of those — and it is one: what stands at
     * {@code result[*]} is what stands at {@code arg0[*][*]}. {@code List.filter},
     * {@code List.sort}, {@code List.take} and {@code List.partition} are the same statement at
     * their own two positions.
     *
     * <p>The one lineage a rule about the output can be pushed back through as it stands, since
     * there is nothing between the two values to push it through.
     *
     * <p><b>Each element of the output is a different one of the source's.</b> Two places in the
     * output are two places in the source, so no element of the source is answered twice: a list
     * holding {@code [x, x]} built from {@code [x, y]} is no list this is true of, though every
     * element of it is the source's own. That is what lets a count say more than a count: as many
     * elements as the source, each a different one of its own, is every one of them once
     * ({@link ElementShape#PERMUTES}), and no more of them is some of them, each once
     * ({@link ElementShape#SUBSET}).
     */
    record SameAs<A>(Source<A> source) implements ElementLineage<A> {

        @Override
        public Source<A> source() {
            return source;
        }
    }

    /**
     * The element is what the closure answered, of an element of the source.
     *
     * <p>{@code List.map}, {@code Set.map}, {@code Map.mapValues}. The input position it came from is
     * known; what value there would put the answer anywhere in particular is not this to say.
     *
     * <p><b>Each element of the result is the closure's answer on an element of the source, and on
     * a different one for each.</b> From {@code [x1, x2]} it does not answer
     * {@code [f(x1), f(x1)]}, though both elements are the closure's answer on an element there.
     * That is what this says and it says nothing more: not that the result has as many elements as
     * the source — {@code Set.map} answers no more, since two elements may map onto one — and so not
     * that every element's answer is there; nothing about the order they come in either. Together
     * with {@link SizeAgainstItsSource#SAME} it is every element's answer, each once
     * ({@link BuiltFrom#mapsEachElementOf}), and a reader wanting the order asks for something
     * nobody declares yet.
     *
     * <p>The closure is handed the element where it takes one, and its key where it takes one;
     * what it is handed at any other parameter — the place {@code List.mapIndexed} hands it — this
     * does not say.
     */
    record ClosureResult<A>(Source<A> source) implements ElementLineage<A> {

        @Override
        public Source<A> source() {
            return source;
        }
    }

    /**
     * The element is inside what the closure answered, of an element of the source.
     *
     * <p>{@code List.flatMap}, whose closure answers a list, and {@code List.filterMap}, whose
     * closure answers an optional. One case for both: what differs is the shape the closure answers
     * with, which its own signature already says.
     */
    record InsideClosureResult<A>(Source<A> source) implements ElementLineage<A> {

        @Override
        public Source<A> source() {
            return source;
        }
    }

    /**
     * The element is one component of an element of the source, which is a tuple.
     *
     * <p>{@code Map.fromList}: every value in the answer is the second component of some entry of
     * the list. It is not one per entry, and it is not every entry's — a later entry under a key
     * replaces an earlier one, so a component of the source may be in no element of the answer. The
     * implication runs from the answer to the source and never back, which is why this says where
     * a value came from and leaves how many there are to {@link SizeAgainstItsSource}.
     *
     * <p>Which entry is left is {@code filedUnder}'s. Entries that agree on that component are one
     * place in the answer and the last of them is what stands there, so a reader that wants every
     * value the source's elements carry to be among the answer's is owed more than this: the
     * entries it knows agree on the component are ones whose other components agree too, and that is
     * the reader's to show of the entries it reads.
     *
     * @param source the argument whose elements are tuples
     * @param index the component, counted from zero as a tuple counts them
     * @param filedUnder the component that tells one place in the answer from another, counted the
     *                   same way, and not {@code index}
     */
    record TupleComponent<A>(Source<A> source, int index, int filedUnder)
            implements ElementLineage<A> {

        public TupleComponent {
            if (index < 0 || filedUnder < 0 || index == filedUnder) {
                throw new IllegalArgumentException("a component and the one it is filed under are"
                        + " two components of a tuple: " + index + ", " + filedUnder);
            }
        }

        @Override
        public Source<A> source() {
            return source;
        }
    }

    /**
     * The element came from any one of these, and nothing here says which.
     *
     * <p>{@code List.append} and a union: every element of the answer was an element of one of the
     * arguments, and the answer holds neither argument's elements alone.
     *
     * <p>Two things can be unsettled and they are not the same thing. Which argument an element came
     * from is one — that is {@code append}, whose alternatives name two arguments. What happened to
     * it on the way is the other: {@code Map.updateIfPresent} answers the map it was given with the
     * value under one key replaced, so every value in its answer came from the argument, and each is
     * either that argument's own value or what the closure made of it. Read as one alternative, it
     * would say of every value what is true of one of them.
     *
     * <p><b>What each element is, and not how many of the source's.</b> The alternatives say where
     * an element may have come from and this says no more: a value the closure made of one element
     * may stand beside that element, so the answer is not each of the source's elements at most
     * once, whatever its alternatives are.
     */
    record OneOf<A>(List<ElementLineage<A>> alternatives) implements ElementLineage<A> {

        public OneOf {
            alternatives = List.copyOf(alternatives);
            if (alternatives.size() < 2) {
                throw new IllegalArgumentException(
                        "one of one place is that place: " + alternatives);
            }
        }

        /**
         * The place they all came from, where they came from one, and null where they did not.
         *
         * <p>Where the alternatives differ in what happened rather than in where it came from, there
         * is one argument to answer with and a reader asking where the elements are from is owed it.
         * Where they name different arguments there is none, and saying so is what keeps a rule
         * about {@code List.append} from being read as a rule about its first argument.
         */
        @Override
        public Source<A> source() {
            Source<A> common = alternatives.get(0).source();
            for (ElementLineage<A> alternative : alternatives) {
                if (common == null || !common.equals(alternative.source())) {
                    return null;
                }
            }
            return common;
        }
    }
}
