package souther.compiler.io;

/**
 * How much looking one request may do in all.
 *
 * <p>A limit on one scan bounds that scan and nothing about how many times a request makes one.
 * Every entry of an archive looked at, in any scan, for any reason, is spent from this; when it is
 * gone the request stops looking. Whoever supplies the archives or the names to look for can then
 * make a request no more expensive than the budget, however they split the work.
 *
 * <p>One request is one thread, so this is not synchronized.
 */
public final class WorkBudget {

    private final long total;
    private long left;

    private WorkBudget(long total) {
        this.total = total;
        this.left = total;
    }

    public static WorkBudget of(long units) {
        return new WorkBudget(units);
    }

    /**
     * Spends {@code units}.
     *
     * @throws LimitExceededException when the budget does not cover them; nothing is left after
     */
    public void spend(long units) throws LimitExceededException {
        if (units > left) {
            left = 0;
            throw new LimitExceededException("more than " + total + " entries looked at in one request");
        }
        left -= units;
    }
}
