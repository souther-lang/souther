package souther.runtime;

/**
 * A computation the run had no room to finish — the platform failing, and not a value being refused.
 *
 * <p>Told apart from {@link ConstraintViolation} on purpose, and the two are easy to confuse because both
 * end a computation that cannot go on. A {@code ConstraintViolation} says something about the model or
 * about a value: a constraint the model declared is broken, or a value has no representation in the
 * carrier asked to hold it (spec §jvm-abort). This says nothing about either. The value is one the type
 * holds, the answer is one the answer's type holds, and what ran out is the room this run was given.
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
 * about the values. Where a type can keep that out of reach it should, by bounding what it stores so that
 * what its own questions want stays inside what the platform builds, which is what {@code Rational} does;
 * this is what is left when that is not enough.
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
