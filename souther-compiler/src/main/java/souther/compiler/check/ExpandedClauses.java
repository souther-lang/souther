package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.TypeKey;

import java.util.List;

/**
 * One declaration's invariant clauses with everything its own module defines substituted, and the
 * operations the language defines left standing ({@link InliningPolicy#DISCHARGE}).
 *
 * <p>That is the whole of what this value says, and it is a property of the tree rather than of who
 * reads it. Two readers already take this form — the invariant-discharge analysis and the codec's
 * constraint mapping — so a name taken from either would be the other's to misread, and a third
 * reader would arrive at a name that was never about it.
 *
 * <p><b>Whose it is.</b> The clauses of a declaration, worked out in the environment of the module
 * that wrote it. Nothing about it depends on who is asking: a module that imports the declaration
 * has no substitution of its own to make, and could not make this one — what a clause names may be
 * a definition its declaring module never exposed, which no importer has a name for
 * (spec §invariant-discharge-representation).
 *
 * <p><b>Why this is not a record.</b> A record's canonical constructor is as public as the record,
 * and what this carries is a list of clauses that anything could supply — which is the whole of what
 * the written tree is too. A reader handed a bare list has nothing to tell the two apart, and that is
 * how a declaration came to be read in whichever representation the reader happened to hold. So the
 * value is minted where it is made and nowhere else: {@link ClauseHelpers} performs the expansion and
 * is the one production site, the way {@link souther.compiler.types.TypeSymbol.AtModule} is minted
 * only by {@code TypeSymbols}.
 */
public final class ExpandedClauses {

    private final TypeKey declaration;
    private final List<Hir.InvariantClause> clauses;

    /** Closed, for the reason written above. */
    ExpandedClauses(TypeKey declaration, List<Hir.InvariantClause> clauses) {
        if (declaration == null) {
            throw new IllegalArgumentException("expanded clauses are some declaration's");
        }
        this.declaration = declaration;
        this.clauses = List.copyOf(clauses);
    }

    /**
     * The clauses of a declaration kind that has no {@code invariant} to write —
     * {@link Hir.SumData} and {@link Hir.UnitData}.
     *
     * <p>Its own way in, and not the empty list handed to the constructor, because it states a
     * different fact. A {@link Hir.Data} with nothing expanded for it is this compiler having failed
     * to hand its own reading over; a sum has nothing to expand at all, and the HIR says so — only
     * {@link Hir.Data} carries {@code invariants()}. Reached through one door the two would be one
     * value and opposite facts.
     */
    static ExpandedClauses nothingToExpand(TypeKey declaration) {
        return new ExpandedClauses(declaration, List.of());
    }

    /** Which declaration these are the clauses of. */
    public TypeKey declaration() {
        return declaration;
    }

    /** Its clauses, in the order they were written, empty where it wrote none. */
    public List<Hir.InvariantClause> clauses() {
        return clauses;
    }

    /**
     * Two of these are one where they are the same clauses of the same declaration.
     *
     * <p>An answer of a query, so what settles it decides what downstream is asked to do again:
     * read as one thing, a declaration whose clauses are what they were leaves every reading of them
     * where it was.
     */
    @Override
    public boolean equals(Object other) {
        return other instanceof ExpandedClauses each
                && declaration.equals(each.declaration) && clauses.equals(each.clauses);
    }

    @Override
    public int hashCode() {
        return declaration.hashCode() * 31 + clauses.hashCode();
    }

    @Override
    public String toString() {
        return declaration.qualified() + " " + clauses.size();
    }
}
