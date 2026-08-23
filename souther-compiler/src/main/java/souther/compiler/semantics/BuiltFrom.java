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
 */
public record BuiltFrom(List<ElementLineage.OutputLineage> outputs, Cardinality size) {

    public BuiltFrom {
        outputs = List.copyOf(outputs);
        if (outputs.isEmpty()) {
            throw new IllegalArgumentException("a construction answers somewhere");
        }
        java.util.Objects.requireNonNull(size, "and answers as many as it answers");
    }

    /** The one place its elements stand, for a construction that answers one run of them. */
    public BuiltFrom(ElementLineage lineage, Cardinality size) {
        this(List.of(new ElementLineage.OutputLineage(
                ElementLineage.ResultPath.elements(), lineage)), size);
    }

    /** Where its elements came from, where they all came from one place. */
    public ElementLineage lineage() {
        if (outputs.size() != 1) {
            throw new IllegalStateException(
                    "a construction answering more than one run of elements was asked for one"
                            + " lineage: " + outputs);
        }
        return outputs.get(0).origin();
    }

    /** Which argument it was built from, where one argument is what it was built from. */
    public ArgumentRef from() {
        ElementLineage.Source source = lineage().source();
        if (source == null) {
            throw new IllegalStateException(
                    "a construction whose elements come from more than one place was asked which"
                            + " one: " + outputs);
        }
        return source.argument();
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
        return wordFor(lineage(), size == Cardinality.SAME);
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
    private ElementShape wordFor(ElementLineage lineage, boolean asMany) {
        return switch (lineage) {
            case ElementLineage.SameAs _ -> asMany ? ElementShape.PERMUTES : ElementShape.SUBSET;
            case ElementLineage.ClosureResult _ ->
                    asMany ? ElementShape.MAPS : ElementShape.COLLAPSES;
            // What the closure answered holds it, so what was stated of the source says nothing
            // of it, and there may be any number of them. No word of the four is about that,
            // and the nearest is the one for elements nothing was kept of.
            case ElementLineage.InsideClosureResult _ -> ElementShape.COLLAPSES;
            case ElementLineage.OneOf one -> {
                if (one.source() == null) {
                    throw new IllegalStateException(
                            "a construction whose elements come from more than one place has no"
                                    + " single source for a shape to be about: " + outputs);
                }
                ElementShape word = null;
                for (ElementLineage alternative : one.alternatives()) {
                    ElementShape read = wordFor(alternative, asMany);
                    word = word == null || word == read ? read : ElementShape.COLLAPSES;
                }
                yield word;
            }
        };
    }
}
