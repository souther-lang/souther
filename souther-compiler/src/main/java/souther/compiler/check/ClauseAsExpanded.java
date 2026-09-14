package souther.compiler.check;

import souther.compiler.ast.Hir;

/**
 * One clause as a reading of it is handed it: the tree, and what the expansion that produced that
 * tree left standing.
 *
 * <p>One value because it is one fact about one tree, and a reading needs both halves of it to say
 * what it can do with a helper applied there — the expansion's answer says the call was meant to
 * stay, and the reading's own scope says whether it can name one
 * ({@link SecondaryClauseReading}).
 *
 * <p><b>Why they travel together.</b> Handed over as two arguments they can be handed over
 * mismatched: a tree from one expansion beside another expansion's answer about what it left, which
 * reads as a limit where nothing was left standing and as this compiler's failure where something
 * was. Nothing downstream could tell, because the tree looks the same either way. So the two are
 * paired where they are known — {@link TypeOps.Declared#asExpanded} and
 * {@link ClausesForDischarge.ClauseReading#asExpanded} — and nothing below takes them apart.
 *
 * @param read the tree the analysis reads
 * @param standing what the expansion that produced {@code read} left standing in it
 */
record ClauseAsExpanded(Hir.Expr read, CallsLeftStanding standing) {

    ClauseAsExpanded {
        if (read == null || standing == null) {
            throw new IllegalArgumentException(
                    "a clause as expanded is a tree and what its expansion left standing");
        }
    }
}
