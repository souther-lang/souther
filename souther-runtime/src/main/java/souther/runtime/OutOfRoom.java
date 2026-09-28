package souther.runtime;

/**
 * A computation the run had no room to finish — the platform failing, and not a value being refused.
 *
 * <p>Told apart from {@link ConstraintViolation} on purpose, and the two are easy to confuse because both
 * end a computation that cannot go on. A {@code ConstraintViolation} says something about the model or
 * about a value: a constraint the model declared is broken, or a value has no representation in the
 * carrier asked to hold it (spec §jvm-abort). This says nothing about either. The value is one the type
 * holds, the answer is one the answer's type holds, and what was short is what this run had to compute it
 * with.
 *
 * <p>Why that distinction is worth a type of its own. A capability like being ordered is a fact about a
 * type, and it is what lets a model write {@code sort}, {@code min} and {@code max} over it. If running
 * out of room were a refusal of the value, then a type would be ordered for some pairs and not others, and
 * what a {@code sort} over it meant — and whether the compiler admitted one at all — would depend on how
 * much room the machine that ran it happened to have. That a given run of one may not finish for want of
 * room is a different thing and is true of every operation there is. So the shortage belongs to the run and
 * is reported as the run's, the way a list longer than memory holds is (ADR-0113).
 *
 * <p>What ran short is the platform's, and room is not the only thing a platform is short of. A computation
 * may want a working number larger than the platform's whole numbers go, which more memory does not answer —
 * and that is still the platform failing to supply what the computation needed rather than anything said
 * about the values. So what this promises is not that more memory would have answered: it is that the
 * operands are owed an answer, and a platform supplying what the decision wanted gives them one.
 *
 * <p>A type must not keep that out of reach by bounding what it stores. The bound would reach every
 * operation that reads a value into the type, and for an exact numeric type that is every heterogeneous
 * operation of the others — so it would refuse values the language says the type holds, and refuse
 * operations whose answer is not of that type, to save a cost. {@code Rational} therefore bounds its stored
 * parts at nothing of its own, and this is what is left.
 *
 * <p>What arrives here is a shortage the runtime found for itself and can say what it was computing when it
 * did. A failure of the virtual machine is not renamed to this: running out of memory is already the
 * platform failing in the platform's own terms, and nothing catches it to dress it as something else.
 *
 * <p>Souther code cannot catch it, as it cannot catch the other aborts. A boundary may, and should read it
 * as the platform failing rather than as anything the request asked for.
 */
public final class OutOfRoom extends RuntimeException {
    private static final long serialVersionUID = 1L;

    public OutOfRoom(String message) {
        super(message);
    }
}
