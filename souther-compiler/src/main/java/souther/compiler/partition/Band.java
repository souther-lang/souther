package souther.compiler.partition;

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
 *              under it starts. Null where they leave it everything that way
 * @param to    the same at the high end
 */
public record Band(Seam under, Seam over, Level from, Level to) {

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
     * Where this run starts, as an end of the position's counts.
     *
     * <p>The one answer, read by everything that has to know how far a run reaches: the classes a
     * position is divided into, and the search that composes a row inside one. Worked out separately
     * they agreed until a run had no value at the end the line is at — a carrier whose values fill
     * has every value past a line and no first one — and then one of them read the run as reaching
     * to the end of the order.
     *
     * <p>Inclusive at a value the run holds, exclusive at the line where the order names none there,
     * and null where nothing stops it that way.
     */
    public souther.compiler.numeric.Endpoint low() {
        if (under == null) {
            return from == null ? null : souther.compiler.numeric.Endpoint.inclusive(placeOf(from));
        }
        return under.above() != null
                ? souther.compiler.numeric.Endpoint.inclusive(placeOf(under.above()))
                : atTheLine(under);
    }

    /** Where it stops, on the same reading. */
    public souther.compiler.numeric.Endpoint high() {
        if (over == null) {
            return to == null ? null : souther.compiler.numeric.Endpoint.inclusive(placeOf(to));
        }
        return over.below() != null
                ? souther.compiler.numeric.Endpoint.inclusive(placeOf(over.below()))
                : atTheLine(over);
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
        return endOf(under, Towards.ABOVE);
    }

    /** The line above it, on the same reading. */
    public souther.compiler.numeric.Endpoint lineAbove(souther.compiler.numeric.Endpoint leaves) {
        if (over == null) {
            return leaves;
        }
        return endOf(over, Towards.BELOW);
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
    private static souther.compiler.numeric.Endpoint endOf(Seam parted, Towards side) {
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

    /**
     * How many digits a search has to look at to find a value of this run.
     *
     * <p>Nothing beyond whole numbers where a line names a value of the quantity — the value beside
     * it is what the run starts at, and it has whatever digits it has. Where a line names none, the
     * digits are what it takes to tell it from the line at the other end: a run between a third and
     * a third and a hundred-billionth holds a decimal, and it is not one anybody would guess a
     * scale for.
     */
    public int digitsToLookIn() {
        if (under == null || over == null) {
            return 0;
        }
        return under.at().digitsToTellApartFrom(over.at());
    }

    /**
     * A range of the position's counts that lies inside this run, for a search to look in.
     *
     * <p>An envelope and never the run itself: what is in the run is the run's to say
     * ({@link #holds}), and this only says where to look. Narrowed inward at a line the quantity
     * has no value at, to a number of {@code digits} digits past it — two thirds is past no whole
     * number below one and is past sixty-six hundredths, so a run between two thirds of a decimal
     * is looked in at the digits it has values at rather than at none.
     */
    public souther.compiler.numeric.NumericDomain.Bounds inside(
            souther.compiler.numeric.Endpoint min, souther.compiler.numeric.Endpoint max,
            int digits) {
        return new souther.compiler.numeric.NumericDomain.Bounds(
                under == null ? min : innerOf(under, low(), Towards.ABOVE, digits),
                over == null ? max : innerOf(over, high(), Towards.BELOW, digits));
    }

    /**
     * One end of the run to look in from.
     *
     * <p>Where the run reaches, which is a value it holds or the line it stops short of — and where
     * the line is at no value of the quantity, the whole number that way, which is in the run
     * because the line is not a number the quantity stands at. Rounded without asking whether the
     * line is one, a run open at a whole number was looked in from that number and the one value
     * offered was the one value it does not hold.
     */
    private static souther.compiler.numeric.Endpoint innerOf(
            Seam parted, souther.compiler.numeric.Endpoint reaches, Towards into, int digits) {
        if (reaches != null) {
            return reaches;
        }
        souther.compiler.numeric.Place inside = parted.at().justBeyond(into, digits);
        return inside == null ? null : souther.compiler.numeric.Endpoint.inclusive(inside);
    }

    /** The line itself, which the run reaches up to and does not hold. Null where the line is at a
     *  place the quantity has no value for, and then nothing here can name where the run stops. */
    private static souther.compiler.numeric.Endpoint atTheLine(Seam parted) {
        Level line = parted.attainedLine();
        return line == null ? null : souther.compiler.numeric.Endpoint.exclusive(placeOf(line));
    }

    private static souther.compiler.numeric.Place placeOf(Level level) {
        return switch (level) {
            case Level.ACount count -> count.at();
            case Level.OnACarrier on -> on.at();
        };
    }

    /** The first value in this run, or null where the order names none there. */
    public Level first() {
        return under == null ? from : under.above();
    }

    /** The last, on the same reading. */
    public Level last() {
        return over == null ? to : over.below();
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
                : under != null ? said(of, under, Towards.ABOVE)
                        : from == null ? "" : of.writtenAt(from) + " <= ";
        String high = except != null && same(except, last())
                ? " < " + of.writtenAt(except)
                : over != null ? said(of, over, Towards.BELOW)
                        : to == null ? "" : " <= " + of.writtenAt(to);
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

    /** Whether this run has any value in it other than {@code except}, where that can be settled.
     *  A run one value wide whose one value is against the line has nothing away from the line. */
    public boolean holdsAnythingBut(Level except) {
        return except == null || first() == null || last() == null
                || !first().key().equals(last().key()) || !same(except, first());
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
        return new Band(below, above, from == null ? null : onto.apply(from),
                to == null ? null : onto.apply(to));
    }

    /**
     * Whether a value of the quantity lies in this run.
     *
     * <p>Both ends included, because a run is named by the values at its ends and not by the lines
     * beside it: the first value above a seam is in the run above and the last value below is in the
     * run below. An end the order supplies rather than a rule leaves that side open.
     *
     * <p>Where a seam names no value on the side facing this run — a carrier whose values fill has
     * no first value above a line it keeps — the run is open at the line itself, which is where the
     * seam's own position says the values part.
     */
    public boolean holds(LevelSpace space, Level value) {
        return past(space, value, under, Towards.ABOVE) && past(space, value, over, Towards.BELOW)
                && within(space, value, from, Towards.ABOVE) && within(space, value, to,
                        Towards.BELOW);
    }

    /** Whether {@code value} is on this run's side of one of the seams that part it. */
    private static boolean past(LevelSpace space, Level value, Seam seam, Towards side) {
        if (seam == null) {
            return true;
        }
        Level edge = side == Towards.ABOVE ? seam.above() : seam.below();
        if (edge != null) {
            return within(space, value, edge, side);
        }
        // No value on this side of the line, so the run is open at the line: what parts the values
        // is the position itself, and every value of the quantity that way is in this run. Asked of
        // the position, because the rule may have written a multiple of the quantity and the value
        // is one of the quantity's own — compared as they stand, a line at a third kept every
        // decimal up to one below it.
        int order = seam.at().compare(value);
        return side == Towards.ABOVE ? order > 0 : order < 0;
    }

    /** Whether {@code value} is at {@code edge} or on the {@code side} of it this run lies. */
    private static boolean within(LevelSpace space, Level value, Level edge, Towards side) {
        if (edge == null) {
            return true;
        }
        int order = space.compare(value, edge);
        return side == Towards.ABOVE ? order >= 0 : order <= 0;
    }

    private static String where(Level at) {
        return at == null ? "" : at.key();
    }
}
