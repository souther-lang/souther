package souther.compiler.semantics;

import java.util.List;

/**
 * Where a construction's elements came from, and how many of them the result has.
 *
 * <p>Named for the proposition it is. {@code Built} said what the value was and not what is true of
 * it, and this package exists to take propositions out of tables named for whoever read them.
 *
 * <p>The lineage is what is declared; {@link #shape} is read off it. The two are not the same
 * statement and the shape is the coarser — {@code List.filterMap} and {@code Set.map} are one shape
 * and two lineages — so declaring the shape and deriving the lineage would be deriving what was
 * thrown away. Written this way round, a reader that wants where an element came from asks
 * {@link ElementLineage} and a reader that wants whether a property survives asks here, and neither
 * is recovering the other's answer.
 *
 * <p><b>Projections and no lookup.</b> Everything below is read off this value and nothing else:
 * which argument the elements are the argument's own, which one each is a closure's answer on. A
 * reader holding one of these has the whole proposition, and what it asks is answered from the
 * proposition rather than by going back to wherever the proposition was found — so the answer is
 * the same whichever table, if any, it was found in.
 *
 * @param <A> the word for an argument of the operation, as {@link ElementLineage} is generic in
 */
public record BuiltFrom<A>(List<ElementLineage.OutputLineage<A>> outputs,
                           SizeAgainstItsSource size) {

    public BuiltFrom {
        outputs = List.copyOf(outputs);
        if (outputs.isEmpty()) {
            throw new IllegalArgumentException("a construction answers somewhere");
        }
        java.util.Objects.requireNonNull(size, "and answers as many as it answers");
    }

    /** The one place its elements stand, for a construction that answers one run of them. */
    public BuiltFrom(ElementLineage<A> lineage, SizeAgainstItsSource size) {
        this(List.of(new ElementLineage.OutputLineage<>(
                ElementLineage.ResultPath.elements(), lineage)), size);
    }

    /** The same proposition with every argument it names read as {@code word} reads it — how it
     *  crosses from the vocabulary it was authored in to the one a reader is handed. */
    public <B> BuiltFrom<B> withArguments(java.util.function.Function<A, B> word) {
        return new BuiltFrom<>(outputs.stream()
                .map(each -> new ElementLineage.OutputLineage<>(each.at(),
                        each.origin().withArguments(word)))
                .toList(), size);
    }

    /** Where its elements came from, where they all came from one place. */
    public ElementLineage<A> lineage() {
        if (outputs.size() != 1) {
            throw new IllegalStateException(
                    "a construction answering more than one run of elements was asked for one"
                            + " lineage: " + outputs);
        }
        return outputs.get(0).origin();
    }

    /** Which argument it was built from, where one argument is what it was built from. */
    public A from() {
        ElementLineage.Source<A> source = lineage().source();
        if (source == null) {
            throw new IllegalStateException(
                    "a construction whose elements come from more than one place was asked which"
                            + " one: " + outputs);
        }
        return source.argument();
    }

    /**
     * The argument the answer holds the elements of, or null where its elements are not the
     * argument's own.
     *
     * <p>The one thing a reader walking backwards from a value needs, and the only part of a lineage
     * that can be walked that way as it stands: where the elements are the same values, an element
     * of the answer is an element of the argument. Where the answer holds what a closure made, the
     * element came from somewhere and is not it, and this says nothing rather than saying where.
     */
    public A holdsTheElementsOf() {
        return outputs.size() == 1
                && lineage() instanceof ElementLineage.SameAs<A> same
                && same.source().elements() == 1
                ? same.source().argument() : null;
    }

    /**
     * The argument each of whose elements the answer holds exactly one closure result of, or null
     * where it answers no such run.
     *
     * <p>The two halves together and neither alone. What the closure answered is the lineage
     * ({@link ElementLineage.ClosureResult}), and that there is one answer per element is the count
     * ({@link SizeAgainstItsSource#SAME}) — two statements about one operation, kept apart because
     * they are different algebras and asked together here because a correspondence needs both.
     * {@code Set.map} has the first and not the second: two elements may answer one, so what its
     * result holds is a subset of what the closure made rather than one per element.
     *
     * <p>Read off the lineage and not off {@link #shape}. The four words are a lossy reading of the
     * pair — {@code List.filterMap} and {@code Set.map} share one — and a correspondence rested on
     * them would be true of operations that do not have it.
     *
     * <p><b>What this licenses is a correspondence and not an order.</b> As many answers as
     * elements, each of them the closure's on one of them; which came first is not stated by either
     * half and is not claimed here.
     */
    public A mapsEachElementOf() {
        if (outputs.size() != 1 || size != SizeAgainstItsSource.SAME) {
            return null;
        }
        ElementLineage<A> lineage = lineage();
        return lineage instanceof ElementLineage.ClosureResult<A>
                && lineage.source().elements() == 1
                ? lineage.source().argument() : null;
    }

    /**
     * The argument the answer holds elements <em>made from</em>, or null where its elements are not
     * made from an argument's.
     *
     * <p>Beside {@link #holdsTheElementsOf} and licensing less. That one says a reader that reached
     * an element of the answer has reached an element of the argument; this says only that the value
     * came from there. What a rule about it means for the position it came from is a question about
     * the closure that made it, and knowing where it came from does not answer it.
     */
    public A derivesItsElementsFrom() {
        if (outputs.size() != 1) {
            return null;
        }
        ElementLineage<A> lineage = lineage();
        return (lineage instanceof ElementLineage.ClosureResult<A>
                || lineage instanceof ElementLineage.InsideClosureResult<A>)
                && lineage.source().elements() == 1 ? lineage.source().argument() : null;
    }

    /**
     * What the building keeps of the elements it was built from, in four words.
     *
     * <p>A projection and the one place it happens. What survives a construction is decided by
     * whether the elements are the source's own and by whether there are as many of them, and both
     * of those are stated above — so the four words are a reading of the pair rather than a fifth
     * thing to keep in step with it.
     */
    public ElementShape shape() {
        return wordFor(lineage(), size == SizeAgainstItsSource.SAME);
    }

    /**
     * The word for one lineage, given whether the result has as many elements as its source.
     *
     * <p>Elements that are each one of several things are each of them read, and the word is the one
     * they all read where they read one — otherwise the word for elements nothing was kept of, which
     * licenses nothing and so is true of a run holding some of each. {@code Map.updateIfPresent} is
     * that: every value is the argument's own or what the closure made of it, so neither
     * {@code PERMUTES} nor {@code MAPS} is true of the run, and what a reader of the four words may
     * assume of it is nothing.
     */
    private ElementShape wordFor(ElementLineage<A> lineage, boolean asMany) {
        return switch (lineage) {
            case ElementLineage.SameAs<A> _ ->
                    asMany ? ElementShape.PERMUTES : ElementShape.SUBSET;
            case ElementLineage.ClosureResult<A> _ ->
                    asMany ? ElementShape.MAPS : ElementShape.COLLAPSES;
            // What the closure answered holds it, so what was stated of the source says nothing
            // of it, and there may be any number of them. No word of the four is about that,
            // and the nearest is the one for elements nothing was kept of.
            case ElementLineage.InsideClosureResult<A> _ -> ElementShape.COLLAPSES;
            case ElementLineage.OneOf<A> one -> {
                if (one.source() == null) {
                    throw new IllegalStateException(
                            "a construction whose elements come from more than one place has no"
                                    + " single source for a shape to be about: " + outputs);
                }
                ElementShape word = null;
                for (ElementLineage<A> alternative : one.alternatives()) {
                    ElementShape read = wordFor(alternative, asMany);
                    word = word == null || word == read ? read : ElementShape.COLLAPSES;
                }
                yield word;
            }
        };
    }
}
