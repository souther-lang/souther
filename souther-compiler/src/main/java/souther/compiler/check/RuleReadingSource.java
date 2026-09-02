package souther.compiler.check;

/**
 * What reading a module's declarations as a static analysis takes: the scope the names resolve in,
 * and the representation the clauses are read in.
 *
 * <p>The two together, because neither answers what a reader of a declaration's rules asks. A scope
 * says what a name means and a representation says which tree the clause is; held apart, a reader
 * that needs both can be given one, and a reading built on the scope alone reads the tree the
 * backend emits from and calls it the declaration's rules.
 *
 * <p>Nothing else goes in here. What a reading may spend is a bound on the work and not part of what
 * is being read ({@link ReadingPolicy}), and it stays a separate argument: joined, how much a
 * declaration may cost and which of its two forms is being read would be one value, and a caller
 * changing either would be changing both.
 *
 * <p>The scope is computed before the representation is — the representation's own query asks for
 * it — so this is where the two meet and not something either of them holds. A scope carrying the
 * representation is a query depending on itself, and holding it lazily hides that rather than
 * resolving it.
 *
 * @param symbols    the module's resolved scope
 * @param invariants the clauses of its declarations as the analysis reads them
 */
public record RuleReadingSource(Symbols symbols, AnalysisInvariants invariants) {

    public RuleReadingSource {
        if (symbols == null || invariants == null) {
            throw new IllegalArgumentException(
                    "reading a declaration's rules takes a scope and a representation");
        }
        if (!symbols.module().equals(invariants.module())) {
            throw new IllegalArgumentException("the scope of " + symbols.module()
                    + " does not read the clauses of " + invariants.module());
        }
    }
}
