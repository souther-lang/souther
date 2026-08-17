package souther.compiler.types;

/**
 * One case a subject can be selected as: the name it is written by, and what the value turns out to
 * be once it has been ({@link Refinement}).
 *
 * <p>A <em>selector</em> rather than a variant or a partition, because one value can satisfy more
 * than one of them. A data may be a case of two named sums declared in its module, and the classes
 * generated for it implement the interface of each, so testing two selectors of one subject can both
 * answer yes. What that means is the reader's to decide — a {@code match} takes the first arm whose
 * selector answers, a behavior's declared relation holds every rule whose selector answers — and
 * nothing here decides it for them.
 */
public record CaseSelector(TypeSymbol name, Refinement refinement) {

    public CaseSelector {
        if (name == null || refinement == null) {
            throw new IllegalArgumentException("a selector is a name and what it refines the value to");
        }
    }

    /** What a value selected by this is read as, or null where nothing readable stands under it. */
    public Type bound() {
        return refinement.bound();
    }
}
