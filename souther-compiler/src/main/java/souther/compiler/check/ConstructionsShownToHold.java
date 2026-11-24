package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.OccurrenceLineage;

import java.util.Set;

/**
 * The constructions of a body the discharge check proved every clause of, on every reading it
 * made of them, by the copy of the construction they are.
 *
 * <p>The check's answer and not a second reading of one. It reads each construction under what
 * holds where it stands — the conditions of the arms above it, and what the declarations say of
 * the values it reads, whatever those values are — so a construction it proved is refused by no
 * run that makes it. A reader asking whether making one may end a run asks this before it reads
 * the clauses again over the input.
 *
 * <p>Every reading of one copy together: a body read once per arm of a split above the
 * construction is read over each arm's runs, and a copy is here where every reading proved it. A
 * copy the check made no reading of is not here, which says nothing of it.
 *
 * @param copies each construction proved, as where it is written and which copy of it it is
 */
public record ConstructionsShownToHold(Set<Copy> copies) {

    /** Nothing proved, which is what a body the check did not read has. */
    public static final ConstructionsShownToHold NONE = new ConstructionsShownToHold(Set.of());

    public ConstructionsShownToHold {
        copies = Set.copyOf(copies);
    }

    /**
     * One copy of a construction: where it is written and which copy of its body it stands in.
     * Where alone puts every copy of a spliced helper's construction under one name, and a
     * reading of one call's copy would be a reading of the other's.
     */
    public record Copy(SourcePos at, OccurrenceLineage lineage) {

        /** The copy {@code made} is. */
        public static Copy of(Core.Construct made) {
            return new Copy(made.pos(), made.lineage());
        }
    }

    /** Whether the check proved every clause of {@code made} on every reading it made of it. */
    public boolean holds(Core.Construct made) {
        return copies.contains(Copy.of(made));
    }
}
