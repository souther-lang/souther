package souther.compiler.partition;

import souther.compiler.numeric.Towards;

/**
 * One run of values a quantity's rules leave between two of the places they part it.
 *
 * <p>What a class of a position is, and what the {@code IN} point of a border beside it asks for.
 * The two used to be derived apart, and only the first of them knew about the lines further along —
 * so a row well past the next line answered for a point that was supposed to be inside this run.
 *
 * @param under the seam this run starts above, or null where nothing parts it there
 * @param over  the seam it stops below, or null on the same reading
 * @param from  what the rules leave the quantity at the low end, which is where a run with no seam
 *              under it starts. Null where they leave it everything that way.
 *              <p>Where it stops and whether it keeps the place it stops at, and not the first value
 *              in it. The two are one thing on a carrier that steps, because a strict end is moved
 *              onto the value it leaves before it is ever read — and on one with no step there is no
 *              such value: {@code value > 0.00m} leaves every decimal above zero and no least one.
 *              Held as the value, such a run either ran to the end of the order or held the very
 *              value its bound refuses, and the class it is came out spelled {@code 0 <= rate}
 * @param to    the same at the high end
 */
public record Band(Seam under, Seam over, Bound from, Bound to) {

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

    /**
     * The same run with every level written the one way, for an identity to be built from.
     *
     * <p>Not {@link #key()}, which reads the run off the values at its ends and so says nothing
     * about where a run with no first value starts: {@code 0 < x} and {@code 5 < x} over the
     * decimals have the same first value, which is none. What holds a run and is compared as a value
     * holds this.
     */
    public Band canonical() {
        return new Band(under == null ? null : under.canonical(),
                over == null ? null : over.canonical(),
                from == null ? null : from.canonical(),
                to == null ? null : to.canonical());
    }

    /**
     * The line below this run, as an end of the position's counts, or the end the rules leave where
     * nothing parts it there.
     *
     * <p>Apart from {@link #low}, and both are this run's own answer about where it starts. One
     * names the first value in it and the other names the line it starts from — on a carrier that
     * steps the two describe one boundary and only the first exists on every carrier, while a class
     * is named after the line an author wrote and not after the value beside it.
     */
    public souther.compiler.numeric.Endpoint lineBelow(souther.compiler.numeric.Endpoint leaves) {
        if (under == null) {
            return leaves;
        }
        return asAnEnd(under, Towards.ABOVE);
    }

    /** The line above it, on the same reading. */
    public souther.compiler.numeric.Endpoint lineAbove(souther.compiler.numeric.Endpoint leaves) {
        if (over == null) {
            return leaves;
        }
        return asAnEnd(over, Towards.BELOW);
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
        return under == null ? valueAt(from) : under.above();
    }

    /** The last, on the same reading. */
    public Level last() {
        return over == null ? valueAt(to) : over.below();
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
        String low = except != null && same(except, first())
                ? of.writtenAt(except) + " < "
                : under != null ? said(of, under, Towards.ABOVE) : leaves(of, from, Towards.ABOVE);
        String high = except != null && same(except, last())
                ? " < " + of.writtenAt(except)
                : over != null ? said(of, over, Towards.BELOW) : leaves(of, to, Towards.BELOW);
        // An end only the rule that drew it can name relates a row to the quantity rather than to
        // the position, so it is a condition of its own beside the rest. Dropped, the run read as
        // reaching past the very line that ends it.
        String ruleLow = low != null ? null : under.asARuleAbout(of::left, Towards.ABOVE);
        String ruleHigh = high != null ? null : over.asARuleAbout(of::left, Towards.BELOW);
        // One subject and two relations where both ends name the same multiple of the quantity,
        // which is what a reader reads a range as. Said as two conditions, the same run reads as
        // two facts — and the class that is this run says it the other way, so a reader is told
        // about one run twice in two voices.
        if (ruleLow != null && ruleHigh != null && sharedMultiple() != null) {
            return ruleLow + " <= " + tail(ruleHigh);
        }
        String plain = (nullToEmpty(low) + of.left() + nullToEmpty(high)).trim();
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
        Seam below = under == null ? null : under.mappedBy(onto);
        Seam above = over == null ? null : over.mappedBy(onto);
        // A line with no place on the other order leaves the run nothing to be read as: which side
        // of it this run lies is the whole of what the run says. An end the carrier does not reach
        // is a different answer and is kept as no end.
        if (under != null && below == null || over != null && above == null) {
            return null;
        }
        return new Band(below, above, mapped(from, onto), mapped(to, onto));
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
     *
     * <p>And the ends the rules leave narrow it further wherever they are the tighter, since a run
     * is what every one of them leaves.
     */
    public LevelRegion region() {
        return LevelRegion.of(new LevelInterval(
                endOf(under, from, Towards.ABOVE), endOf(over, to, Towards.BELOW)));
    }

    /**
     * One end of this run, from the line that parts it there and the end the rules leave.
     *
     * <p>Whichever of the two is the tighter, because a run is on this side of the line and inside
     * what the rules leave at once. Read as one or the other, a run bounded by a rule and parted by
     * a line reached past whichever of them was not consulted.
     */
    private static Bound endOf(Seam parted, Bound left, Towards side) {
        if (parted == null) {
            return left;
        }
        Level edge = side == Towards.ABOVE ? parted.above() : parted.below();
        // The value beside the line where the quantity has one, and the line itself where it has
        // none. Written as the line, the run above a seam that keeps its own value would hold that
        // value; written as the value, a run over an order whose values fill would have no end at
        // all.
        Bound atTheLine = edge != null ? Bound.at(edge, true) : new Bound(parted.at(), false);
        return side == Towards.ABOVE ? Bound.lower(atTheLine, left) : Bound.upper(atTheLine, left);
    }

    /** Whether a value of the quantity lies in this run. */
    public boolean holds(Level value) {
        return region().contains(value);
    }

    private static String where(Level at) {
        return at == null ? "" : at.key();
    }
}
