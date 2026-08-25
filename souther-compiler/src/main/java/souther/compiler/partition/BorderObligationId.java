package souther.compiler.partition;

/**
 * What a row is owed for: one line the author wrote, wherever it is read.
 *
 * <p>The key evidence is interchangeable under. Two readings are one debt when a row standing at
 * either establishes what a row standing at the other would, and that is a property of the line and
 * not of the reading — so {@code UserId}'s clause saying a user id is a string of one character or
 * more is one row to write, whether the position it was read at is {@code draft.owner} or
 * {@code activities[*]@CallTask.owner}, and whether the behavior carrying it is {@code scheduleMeeting}
 * or {@code touchCount}. Neither behavior says anything about the length of a user id, so neither
 * can disagree with the other about a row at length 1 (issue #1062).
 *
 * <p><b>Not the rule.</b> One clause places two ends: {@code invariant within = value >= 1 && value
 * <= 10} is one {@link souther.compiler.check.RuleRef.Invariant} and two lines, and a row at the
 * bottom of the range is no evidence about the top. Keyed on the rule, the author writes one row and
 * the other end goes quiet.
 *
 * <p><b>Not the level either.</b> Two rules can cut at one value on one carrier — a record stopping
 * a {@code Minute} at 1000 and another record stopping it at the same 1000 — and each is a rule the
 * author could change without touching the other. That is the accounting {@link OriginRef} already
 * keeps for cuts, and it is kept here for the same reason.
 *
 * <p><b>And not where it was read.</b> The quantity a line was met on — which position of which
 * behavior — is the occurrence, one per position of every behavior carrying the type. It is what
 * {@link Border#cut()} holds, and holding it here is what asked for one clause's row 126 times over
 * {@code crm}'s {@code UserId}.
 *
 * <p>Three identities and not one, the way {@link souther.compiler.coverage.CoverageSites.Obligation}
 * and {@link souther.compiler.coverage.ControlPointId} are on the arm side. {@link OriginRef#rule()}
 * answers which rule of the model this came from and is provenance; this answers which debt it is;
 * {@link Border} answers where it was read. A narrowing moves the second without moving the first:
 * {@code MinuteOfDay}'s maximum is the same rule whether or not {@code WorkInterval} moved where it
 * lands, and the line the two settled together is not the line the bound would have drawn alone — so
 * it comes back the same from {@code rule()} and different from here.
 *
 * @param origin the rule that drew the line, as the reading met it — narrowings and all, because a
 *               narrowed end is a distinction the narrowing declarations authored and not one the
 *               bound authored on its own
 * @param at     where on the quantity it cut. A level and not a place: what a line is drawn on is
 *               not always a position, and two of the three shapes count something no position holds
 */
public record BorderObligationId(OriginRef origin, Level at) {

    public BorderObligationId {
        if (origin == null || at == null) {
            throw new IllegalArgumentException(
                    "a debt is some rule's line somewhere: " + origin + " " + at);
        }
    }

    /**
     * Which rule of the model this came from, through however many narrowings.
     *
     * <p>Provenance, and never a key. Offered here so that a reader wanting to say what drew the
     * line does not reach past this into the origin and come back holding something that groups.
     */
    public souther.compiler.check.RuleRef provenance() {
        return origin.rule();
    }
}
