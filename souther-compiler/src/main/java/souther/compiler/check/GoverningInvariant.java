package souther.compiler.check;

/**
 * One clause that governs a data, and which clause it is.
 *
 * <p>A settled clause does not say which declaration wrote it: whoever holds one asked a declaration
 * for it. The clauses that govern a data are the clauses of every declaration its spreads reach, put
 * in one list, and the list is where that asking is no longer in sight. So each one is handed on with
 * the declaration and the place it has there, which is what another reading of the same clause is
 * matched to it by.
 *
 * @param id which clause of which declaration this is
 * @param settled the clause as it was settled, with what its expansion left standing
 */
public record GoverningInvariant(Clause.Id id, SettledInvariant settled) {

    public GoverningInvariant {
        if (id == null || settled == null) {
            throw new IllegalArgumentException("a governing clause is which clause and the clause");
        }
    }
}
