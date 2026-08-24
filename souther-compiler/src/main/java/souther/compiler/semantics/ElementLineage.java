package souther.compiler.semantics;

import java.util.List;

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
 */
public sealed interface ElementLineage {

    /**
     * The argument an operation's answer holds the elements of, or null where its elements are not
     * the argument's own.
     *
     * <p>The one thing a reader walking backwards from a value needs, and the only part of a lineage
     * that can be walked that way as it stands: where the elements are the same values, an element
     * of the answer is an element of the argument. Where the answer holds what a closure made, the
     * element came from somewhere and is not it, and this says nothing rather than saying where.
     *
     * <p>Asked here and not of the reader that happens to hold the table today. What an operation
     * does to the values it is given is declared once and read by whoever has a use for it; a caller
     * reaching through the invariant-discharge check for it would depend on that check to learn what
     * the library says.
     */
    static ArgumentRef holdsTheElementsOf(souther.compiler.types.ValueName operation) {
        BuiltFrom built = OperationFacts.buildsItsResultFrom(operation);
        return built != null && built.outputs().size() == 1
                && built.lineage() instanceof SameAs same
                && same.source().elements() == 1
                ? same.source().argument() : null;
    }

    /**
     * The argument an operation's answer holds elements <em>made from</em>, or null where its
     * elements are not made from an argument's.
     *
     * <p>Beside {@link #holdsTheElementsOf} and licensing less. That one says a reader that reached
     * an element of the answer has reached an element of the argument; this says only that the value
     * came from there. What a rule about it means for the position it came from is a question about
     * the closure that made it, and knowing where it came from does not answer it.
     */
    static ArgumentRef derivesItsElementsFrom(souther.compiler.types.ValueName operation) {
        BuiltFrom built = OperationFacts.buildsItsResultFrom(operation);
        if (built == null || built.outputs().size() != 1) {
            return null;
        }
        ElementLineage lineage = built.lineage();
        return (lineage instanceof ClosureResult || lineage instanceof InsideClosureResult)
                && lineage.source().elements() == 1 ? lineage.source().argument() : null;
    }

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
    record OutputLineage(ResultPath at, ElementLineage origin) {}

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
    record Source(ArgumentRef argument, int elements) {

        public Source {
            if (elements < 1) {
                throw new IllegalArgumentException(
                        "a lineage is about the elements of something: " + elements);
            }
        }
    }

    /** Where the elements this is about come from, or null where they come from more than one
     *  place. */
    Source source();

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
     */
    record SameAs(Source source) implements ElementLineage {

        @Override
        public Source source() {
            return source;
        }
    }

    /**
     * The element is what the closure answered, of an element of the source.
     *
     * <p>{@code List.map}, {@code Set.map}, {@code Map.mapValues}. The input position it came from is
     * known; what value there would put the answer anywhere in particular is not this to say.
     */
    record ClosureResult(Source source) implements ElementLineage {

        @Override
        public Source source() {
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
    record InsideClosureResult(Source source) implements ElementLineage {

        @Override
        public Source source() {
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
     */
    record OneOf(List<ElementLineage> alternatives) implements ElementLineage {

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
        public Source source() {
            Source common = alternatives.get(0).source();
            for (ElementLineage alternative : alternatives) {
                if (common == null || !common.equals(alternative.source())) {
                    return null;
                }
            }
            return common;
        }
    }
}
