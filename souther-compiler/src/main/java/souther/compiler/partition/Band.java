package souther.compiler.partition;

import souther.compiler.numeric.Towards;

/**
 * One run of values a quantity's rules leave between two of the places they part it.
 *
 * <p>What a class of a position is, and what the {@code IN} point of a border beside it asks for.
 * The two used to be derived apart, and only the first of them knew about the lines further along —
 * so a row well past the next line answered for a point that was supposed to be inside this run.
 *
 * <p>Both ends are always there, and each says what stops the run ({@link BandEnd}). They used to be
 * a line that might be null beside an end the rules leave that might be null, and what a run stops
 * at was read back out of which of the four combinations had turned up.
 *
 * @param lower what stops the run at the low end
 * @param upper the same at the high end
 */
public record Band(BandEnd lower, BandEnd upper) {

    public Band {
        if (lower == null || upper == null) {
            throw new IllegalArgumentException(
                    "a run stops somewhere at both ends, or runs to the end of the order: "
                            + lower + " " + upper);
        }
    }

    /**
     * One end of a run, from the line that parts the values there and the end the rules leave.
     *
     * <p>Both are consulted, because a run is on this side of the line and inside what the rules
     * leave at once: a run parted by a line the rules stop short of reaches the rules' end. Which of
     * the two named the run is a different question and is the shape's ({@link BandEnd.AtParting}
     * names the line whether or not the run reaches it).
     *
     * @param inward which way the run lies from this end
     */
    public static BandEnd endAt(Seam parted, Bound leaves, Towards inward) {
        if (parted == null) {
            return leaves == null ? new BandEnd.AtOrderEnd(inward.opposite())
                    : new BandEnd.AtDomain(leaves);
        }
        return new BandEnd.AtParting(parted, tighter(atTheLine(parted, inward), leaves, inward));
    }

    /**
     * Where a line lets the run beside it start.
     *
     * <p>The value beside the line where the quantity has one, and the line itself where it has
     * none. Written as the line, the run above a seam that keeps its own value would hold that
     * value; written as the value, a run over an order whose values fill would have no end at all.
     */
    private static Bound atTheLine(Seam parted, Towards inward) {
        Level edge = inward == Towards.ABOVE ? parted.above() : parted.below();
        return edge != null ? Bound.at(edge, true) : new Bound(parted.at(), false);
    }

    private static Bound tighter(Bound line, Bound leaves, Towards inward) {
        return inward == Towards.ABOVE ? Bound.lower(line, leaves) : Bound.upper(line, leaves);
    }

    /**
     * How this run reads: the first value in it and the last.
     *
     * <p>Taken from the seams either side rather than held, so that a run and the places that part
     * it can never say different things about where it starts. An end the order itself supplies is
     * written as nothing, because there is no value there to name.
     */
    public String key() {
        return where(first()) + "|" + where(last());
    }

    /** The same run with every level written the one way, for an identity to be built from.
     *
     * <p>Not {@link #key()}, which reads the run off the values at its ends and so says nothing
     * about where a run with no first value starts: {@code 0 < x} and {@code 5 < x} over the
     * decimals have the same first value, which is none. What holds a run and is compared as a value
     * holds this. */
    public Band canonical() {
        return new Band(canonical(lower), canonical(upper));
    }

    private static BandEnd canonical(BandEnd end) {
        return switch (end) {
            case BandEnd.AtParting(Seam parted, Bound reaches) ->
                    new BandEnd.AtParting(parted.canonical(), reaches.canonical());
            case BandEnd.AtDomain(Bound reaches) -> new BandEnd.AtDomain(reaches.canonical());
            case BandEnd.AtOrderEnd order -> order;
        };
    }

    /**
     * The line below this run, as an end of the position's counts, or the end the rules leave where
     * nothing parts it there.
     *
     * <p>Apart from the first value in it, and both are this run's own answer about where it starts.
     * One names the first value and the other names the line it starts from — on a carrier that
     * steps the two describe one boundary and only the first exists on every carrier, while a class
     * is named after the line an author wrote and not after the value beside it.
     */
    public souther.compiler.numeric.Endpoint lineBelow(souther.compiler.numeric.Endpoint leaves) {
        return lineAt(lower, Towards.ABOVE, leaves);
    }

    /** The line above it, on the same reading. */
    public souther.compiler.numeric.Endpoint lineAbove(souther.compiler.numeric.Endpoint leaves) {
        return lineAt(upper, Towards.BELOW, leaves);
    }

    /**
     * One end of the run as an end of the position's counts.
     *
     * <p>{@code leaves} is what the rules leave the quantity, for a run built without being told —
     * an arrangement made of the lines alone has no end to give, and its outermost runs are open
     * ({@link Intervals} builds one and holds it to the range afterwards). A run that was told keeps
     * its own answer, so the two cannot say different things about one end.
     */
    private static souther.compiler.numeric.Endpoint lineAt(
            BandEnd end, Towards inward, souther.compiler.numeric.Endpoint leaves) {
        return switch (end) {
            case BandEnd.AtParting parted -> asAnEnd(parted.seam(), inward);
            case BandEnd.AtDomain domain -> new souther.compiler.numeric.Endpoint(
                    placeOf(valueOrRefuse(domain.reaches())), domain.reaches().inclusive());
            case BandEnd.AtOrderEnd _ -> leaves;
        };
    }

    /**
     * A line as the end of the run on one side of it.
     *
     * <p>Named by the line itself where the quantity has a value there, and by the value beside it
     * where it has none: {@code 2 * n <= 9} parts the whole numbers at four and a half, which no
     * whole number is, and the classes either side of it are still {@code x <= 4} and {@code 4 < x}.
     * Read only off the line, such a class had no name at all; read only off the values beside it, a
     * class an author wrote {@code <= 4} for came back spelled {@code < 5}.
     */
    private static souther.compiler.numeric.Endpoint asAnEnd(Seam parted, Towards side) {
        Level line = parted.attainedLine();
        if (line != null) {
            return new souther.compiler.numeric.Endpoint(placeOf(line),
                    side == Towards.ABOVE ? !parted.keepsItsOwnValueBelow()
                            : parted.keepsItsOwnValueBelow());
        }
        // The values either side of the line, which say the same thing where the line has no name of
        // its own. The one below where the order has it, since that is the number an author reading
        // a class of whole numbers expects to see.
        Level named = parted.below() != null ? parted.below() : parted.above();
        if (named == null) {
            return null;
        }
        boolean below = named == parted.below();
        return new souther.compiler.numeric.Endpoint(placeOf(named),
                side == Towards.ABOVE ? !below : below);
    }

    private static souther.compiler.numeric.Place placeOf(Level level) {
        return switch (level) {
            case Level.ACount count -> count.at();
            case Level.OnACarrier on -> on.at();
        };
    }

    /** The first value in this run, or null where the order names none there. */
    public Level first() {
        Seam parted = lower.seam();
        return parted == null ? valueAt(left(lower)) : parted.above();
    }

    /** The last, on the same reading. */
    public Level last() {
        Seam parted = upper.seam();
        return parted == null ? valueAt(left(upper)) : parted.below();
    }

    /** What the rules leave the quantity at this end, where that is what stops the run and there is
     *  an end at all. */
    private static Bound left(BandEnd end) {
        return end instanceof BandEnd.AtDomain domain ? domain.reaches() : null;
    }

    /**
     * The value an end the rules leave stands at, where the run holds it and the quantity has one
     * there.
     *
     * <p>Null for an end the run stops short of, which is what a strict bound on a carrier with no
     * step leaves: the run has no first value, and saying it starts at the bound's own would put the
     * one value the rule refuses inside it.
     */
    private static Level valueAt(Bound end) {
        return end == null || !end.inclusive() ? null : end.at().asALevelOfTheQuantity();
    }

    /**
     * This run as a report writes it, in the same words the class of a position that is this run is
     * named by.
     *
     * <p>Written from the lines either side rather than from the values at its ends, which is what
     * lets one spelling answer for every carrier: a run above a line at ten is {@code 10 < x} on the
     * whole numbers and on the decimals alike, while the value it starts at exists only on the
     * first. One spelling, so that the class a report counts and the point a border owes inside it
     * are visibly the same run.
     */
    public String written(BorderQuantity of) {
        return written(of, null);
    }

    /**
     * The same, without one value of it.
     *
     * <p>Which is what a point away from a border asks for: the run, less the value against the
     * line. Said as the run alone, a reader is told to write a row anywhere up to a hundred when a
     * hundred is the one value that will not do.
     */
    public String written(BorderQuantity of, Level except) {
        return written(of, except, of::left);
    }

    /**
     * The same, with {@code much} in place of how the quantity says a multiple of itself here.
     *
     * <p>For a debt, which is written on what the declaration wrote rather than on the position some
     * reading met the line at: a run of {@code UserId}'s lengths reads {@code 1 <
     * String.length(value)} wherever it is owed, and taking the name off a reading would put
     * whichever position a walk reached first into a sentence about the type (issue #1062).
     *
     * <p>A multiple and not a name, because an end only the rule that drew it can name says how much
     * of the quantity that rule wrote — and how a quantity says twice itself is the quantity's own
     * answer ({@link BorderQuantity#left(java.math.BigDecimal)}).
     *
     * <p>The levels are still the reading's to write, because the order they are on is what knows
     * how to spell them, and it is the same order at every reading of one line.
     */
    public String written(BorderQuantity of, Level except,
                          java.util.function.Function<java.math.BigDecimal, String> much) {
        String left = much.apply(java.math.BigDecimal.ONE);
        Seam under = lower.seam();
        Seam over = upper.seam();
        String low = except != null && same(except, first())
                ? of.writtenAt(except) + " < "
                : under != null ? said(of, under, Towards.ABOVE)
                        : leaves(of, left(lower), Towards.ABOVE);
        String high = except != null && same(except, last())
                ? " < " + of.writtenAt(except)
                : over != null ? said(of, over, Towards.BELOW)
                        : leaves(of, left(upper), Towards.BELOW);
        // An end only the rule that drew it can name relates a row to the quantity rather than to
        // the position, so it is a condition of its own beside the rest. Dropped, the run read as
        // reaching past the very line that ends it.
        String ruleLow = low != null ? null : under.asARuleAbout(much, Towards.ABOVE);
        String ruleHigh = high != null ? null : over.asARuleAbout(much, Towards.BELOW);
        // One subject and two relations where both ends name the same multiple of the quantity,
        // which is what a reader reads a range as. Said as two conditions, the same run reads as
        // two facts — and the class that is this run says it the other way, so a reader is told
        // about one run twice in two voices.
        if (ruleLow != null && ruleHigh != null && sharedMultiple() != null) {
            return ruleLow + " <= " + tail(ruleHigh);
        }
        String plain = (nullToEmpty(low) + left + nullToEmpty(high)).trim();
        boolean anyPlain = low != null && !low.isEmpty() || high != null && !high.isEmpty();
        java.util.List<String> said = new java.util.ArrayList<>();
        if (ruleLow != null) {
            said.add(ruleLow);
        }
        if (anyPlain) {
            said.add(plain);
        }
        if (ruleHigh != null) {
            said.add(ruleHigh);
        }
        return said.isEmpty() ? "any" : String.join(" and ", said);
    }

    /** What a condition says after the subject it is about, which is what the compact form keeps
     *  of the upper end. */
    private static String tail(String said) {
        int at = said.indexOf("<=");
        return said.substring(at + 3);
    }

    private static String nullToEmpty(String said) {
        return said == null ? "" : said;
    }

    /**
     * One end of the run as a report writes it: the line where the quantity has a value there, and
     * the value beside it where it has none.
     *
     * <p>The same reading {@link #lineBelow} gives in the position's own counts. Written off the
     * level the rule was written with, a run parted by a rule that wrote a multiple of the quantity
     * asked the quantity to write a number that is not one of its values.
     */
    private static String said(BorderQuantity of, Seam parted, Towards side) {
        Level line = parted.attainedLine();
        if (line != null) {
            return side == Towards.ABOVE ? of.writtenAt(line) + opens(parted)
                    : closes(parted) + of.writtenAt(line);
        }
        Level named = parted.below() != null ? parted.below() : parted.above();
        if (named != null) {
            boolean below = named == parted.below();
            return side == Towards.ABOVE
                    ? of.writtenAt(named) + (below ? " < " : " <= ")
                    : (below ? " <= " : " < ") + of.writtenAt(named);
        }
        // Nothing names this end but the rule that drew it, which is the same sentence the class
        // this run is gets. Marked so the caller writes it as a condition of its own: it names the
        // quantity itself, and a run with one such end and one plain one relates a row to two
        // things.
        return null;
    }

    /**
     * One end of the run as the rules leave it, where no line parts the values there.
     *
     * <p>The relation is the end's own: a bound that keeps the place it stops at reads {@code <=},
     * and one that stops short of it reads {@code <}. Written as {@code <=} either way, the class a
     * strict bound on a carrier with no step leaves was spelled as holding the very value the rule
     * refuses.
     */
    private static String leaves(BorderQuantity of, Bound end, Towards side) {
        if (end == null) {
            return "";
        }
        Level at = valueOrRefuse(end);
        return side == Towards.ABOVE
                ? of.writtenAt(at) + (end.inclusive() ? " <= " : " < ")
                : (end.inclusive() ? " <= " : " < ") + of.writtenAt(at);
    }

    private static boolean same(Level one, Level other) {
        return one != null && other != null && one.key().equals(other.key());
    }

    /**
     * What both ends of this run relate a row to, where they relate it to the same thing.
     *
     * <p>A run written as two conditions reads as two facts, and a run written as one subject
     * between two relations reads as the range it is. Which is available exactly where neither end
     * has a value to be named by and both name the same multiple of the quantity — the decision is
     * the run's, and what each reader calls that multiple is the reader's.
     *
     * <p>Null where they do not, and then the two conditions are said as two: a run between a line
     * on the position and a line on a multiple of it relates a row to both.
     */
    public java.math.BigDecimal sharedMultiple() {
        Seam under = lower.seam();
        Seam over = upper.seam();
        if (under == null || over == null
                || under.attainedLine() != null || over.attainedLine() != null
                || under.below() != null || under.above() != null
                || over.below() != null || over.above() != null) {
            return null;
        }
        java.math.BigDecimal[] below = under.at().asARule();
        java.math.BigDecimal[] above = over.at().asARule();
        return below != null && above != null && below[0].compareTo(above[0]) == 0
                ? below[0] : null;
    }

    /** Whether the line below this run keeps its own value, which decides whether the run starts
     *  past that value or at it. */
    private static String opens(Seam under) {
        return keepsItsOwnValueBelow(under) ? " < " : " <= ";
    }

    private static String closes(Seam over) {
        return keepsItsOwnValueBelow(over) ? " <= " : " < ";
    }

    private static boolean keepsItsOwnValueBelow(Seam seam) {
        return seam.keepsItsOwnValueBelow();
    }

    /**
     * The same run, read on another order.
     *
     * <p>Everything that says where the run is moves together: the lines either side of it and the
     * ends the rules leave. What this exists for is a rule between two positions, whose run is a
     * run of distances until the other end of it is known.
     */
    Band mappedBy(java.util.function.UnaryOperator<Level> onto) {
        BandEnd low = mappedBy(lower, Towards.ABOVE, onto);
        BandEnd high = mappedBy(upper, Towards.BELOW, onto);
        // A line with no place on the other order leaves the run nothing to be read as: which side
        // of it this run lies is the whole of what the run says. An end the carrier does not reach
        // is a different answer and is kept as no end.
        if (low == null || high == null) {
            return null;
        }
        return new Band(low, high);
    }

    private static BandEnd mappedBy(BandEnd end, Towards inward,
                                    java.util.function.UnaryOperator<Level> onto) {
        return switch (end) {
            case BandEnd.AtParting(Seam parted, Bound reaches) -> {
                Seam moved = parted.mappedBy(onto);
                if (moved == null) {
                    yield null;
                }
                // Where the run reaches is worked out again from what moved, because the two things
                // it is the tighter of move by different rules: a line goes through the seam, and an
                // end the rules leave is at a value of the quantity and goes through that.
                //
                // Asked with the records' own equality, which is the question here: whether this
                // reach is the one built from the line, and not whether the two are one place. A
                // reach that came off the rules' end is at the same place under another spelling as
                // often as not, and either answer takes the same branch.
                yield new BandEnd.AtParting(moved, reaches.equals(atTheLine(parted, inward))
                        ? atTheLine(moved, inward)
                        : tighter(atTheLine(moved, inward), mapped(reaches, onto), inward));
            }
            case BandEnd.AtDomain(Bound reaches) -> new BandEnd.AtDomain(mapped(reaches, onto));
            case BandEnd.AtOrderEnd order -> order;
        };
    }

    /** An end the rules leave, read on another order. Whether the run keeps the place it stops at
     *  is the end's own and does not move with it. */
    private static Bound mapped(Bound end, java.util.function.UnaryOperator<Level> onto) {
        return end == null ? null : Bound.at(onto.apply(valueOrRefuse(end)), end.inclusive());
    }

    /**
     * Where an end the rules leave stands, as a value of the quantity.
     *
     * <p>Always one. Such an end comes off a bound the rules wrote about the quantity itself, so it
     * is at a level of it — unlike a line, which a rule may draw at a place the quantity stands at
     * no value of ({@code 3 * d <= 1} cuts at a third). A place with no value has an answer where a
     * line has one, and it has none here: there is no seam to name it by. So it is refused rather
     * than written as no end at all, which would leave the run reaching past what the rules leave.
     */
    private static Level valueOrRefuse(Bound end) {
        Level at = end.at().asALevelOfTheQuantity();
        if (at == null) {
            throw new IllegalStateException(
                    "an end the rules leave, at no value of the quantity: " + end);
        }
        return at;
    }

    /**
     * The values this run is, as a set.
     *
     * <p>The one answer about what is in it, which everything that asks goes through — whether a
     * value is in it, whether it holds anything, and where to look for a row. Worked out again by
     * each of them, what was in a run and what was looked for in it came apart wherever the run's
     * ends are lines the quantity stands at no value of (issue #903).
     *
     * <p>Both ends included where a value names them, because a run is named by the values at its
     * ends and not by the lines beside it: the first value above a seam is in the run above and the
     * last value below is in the run below. Where a seam names no value on the side facing this run
     * — a carrier whose values fill has no first value above a line it keeps — the run is open at
     * the line itself, which is where the seam's own position says the values part.
     */
    public LevelRegion region() {
        return LevelRegion.of(new LevelInterval(lower.reaches(), upper.reaches()));
    }

    /** Whether a value of the quantity lies in this run. */
    public boolean holds(Level value) {
        return region().contains(value);
    }

    private static String where(Level at) {
        return at == null ? "" : at.key();
    }
}
