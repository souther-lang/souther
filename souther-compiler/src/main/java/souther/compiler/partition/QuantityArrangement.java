package souther.compiler.partition;

import souther.compiler.numeric.Towards;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Where every rule about one quantity parts its values, and the runs they leave between them.
 *
 * <p><b>One arrangement per quantity, made once.</b> What the classes of a position are, what a
 * border owes at each of its points and what the generator offers rows for are three readings of
 * this and not three derivations of it. Derived separately, the partition merged every threshold on
 * a position into one set of ranges while a border was built from one rule at a time — so a border
 * knew nothing of the lines beside it, and the run its {@code IN} point asked for ran past them to
 * the end of the order.
 *
 * <p><b>Built from seams and never from thresholds.</b> Several rules can part a quantity's values
 * in one place, and they are one place however they were written: {@code n <= 4} and {@code n < 5}
 * divide the whole numbers once. Keyed on the numbers the rules carry, they leave a run above four
 * and below five that no row can be written in, and a report counts a class nothing can reach
 * ({@link Seam}).
 *
 * @param partings where the values part and which lines the model wrote there, in the order the
 *                 values are in
 * @param runs     the runs between them, one more than there are partings
 */
public record QuantityArrangement(List<Parting> partings, List<Run> runs) {

    public QuantityArrangement {
        partings = List.copyOf(partings);
        runs = List.copyOf(runs);
    }

    /**
     * One run of the arrangement, with what stops it at each end as a row inside it is owed to it.
     *
     * <p>Beside the run's own values rather than inside them. What a row has to do to be inside is
     * the run ({@link Band}), and what it is owed to is which rules stopped it — two questions, and
     * a value that answered both would have the second inside every comparison of the first.
     *
     * @param values what a row inside it has to be
     * @param below  the place the values part at the low end, or null where nothing parts them there
     * @param above  the same at the high end
     */
    public record Run(Band values, Parting below, Parting above) {

        public Run {
            if (values == null) {
                throw new IllegalArgumentException("a run is a run of values");
            }
            agree(values.lower(), below, Towards.BELOW);
            agree(values.upper(), above, Towards.ABOVE);
        }

        /**
         * That the run and the place it stops at say the same thing about one end.
         *
         * <p>Checked rather than derived, because they are put here by one caller out of two
         * readings of the arrangement: the run is what the values come to and the place is what the
         * model wrote, and an end that is a line in one and not in the other is those two readings
         * having come apart.
         */
        private static void agree(BandEnd end, Parting parted, Towards side) {
            if ((end instanceof BandEnd.AtParting) != (parted != null)) {
                throw new IllegalArgumentException("a run parted at its " + side
                        + " end and no line there, or a line and no parting: " + end + " " + parted);
            }
            if (parted != null && !parted.geometry().key().equals(end.seam().key())) {
                throw new IllegalArgumentException("a run stopping at one place and a line at"
                        + " another: " + end.seam().key() + " against " + parted.key());
            }
        }

        /**
         * What a row inside this run is owed to at one end: one answer per rule that could have
         * stopped it there, and one where no rule did.
         *
         * <p>Each line at a place is enough on its own to have stopped the run — taking either of
         * two away leaves it where it is — so each is one thing a row here answers for. An end the
         * rules leave together and an end of the order are one answer apiece, neither being any one
         * rule's doing.
         */
        public List<FarEnd> endsAt(Towards side) {
            BandEnd end = side == Towards.ABOVE ? values.upper() : values.lower();
            Parting parted = side == Towards.ABOVE ? above : below;
            return switch (end) {
                case BandEnd.AtParting at -> parted.alternatives().stream()
                        .map(line -> (FarEnd) new FarEnd.AtALine(line, at.seam())).toList();
                case BandEnd.AtDomain at -> List.of(new FarEnd.AtTheDomain(at.reaches()));
                case BandEnd.AtOrderEnd at -> List.of(new FarEnd.AtTheOrderEnd(at.towards()));
            };
        }
    }

    /** The runs as what a row inside each has to be, for a reader that is not asking what any of
     *  them is owed to. */
    public List<Band> bands() {
        return runs.stream().map(Run::values).toList();
    }

    /**
     * The arrangement {@code parted} come to on {@code space}.
     *
     * <p>Ordered here rather than by the caller, and deduplicated by where the values part rather
     * than by which rule parted them: the rules that drew a place are a property of the place and
     * are kept beside it, while what the quantity is divided into is a property of the quantity.
     */
    public static QuantityArrangement of(LevelSpace space, List<Parting> parted) {
        return of(space, parted, null, null);
    }

    /**
     * The same, where the rules leave the quantity only what runs from {@code from} to {@code to}.
     *
     * <p>The ends are not seams and never become runs of their own. Nothing outside a bound can be
     * constructed, so there is no run on the far side of one to cover (ADR-0090); what a bound does
     * is stop the run beside it, which is why the two either side of a line at ten run from the
     * bound rather than from the order's own extent.
     *
     * @param from where the rules leave off at the low end and whether they keep the place they
     *             leave off at, or null where they leave it everything that way. Not the first value
     *             in the run: a strict bound on a carrier with no step leaves no first value, and
     *             read as one such a run either had no end at all or held the value its bound
     *             refuses
     * @param to   the same at the high end
     */
    public static QuantityArrangement of(LevelSpace space, List<Parting> parted, Bound from,
                                         Bound to) {
        Map<String, Parting> distinct = new LinkedHashMap<>();
        for (Parting each : parted) {
            // A place the rules leave nothing at divides nothing. The values it would tell apart are
            // values no row can be written at, so it is dropped rather than kept as a run holding
            // none — which is a class an author would be told to write a row for and could not.
            if (outside(each.geometry(), from, to)) {
                continue;
            }
            // One place, and every line the model wrote there against it. Which is the whole of what
            // this being the one canonicaliser buys: a producer that told two candidates apart for
            // itself kept whichever it read first, and the other line went unsaid.
            distinct.merge(each.key(), each, Parting::and);
        }
        List<Parting> ordered = new ArrayList<>(distinct.values());
        ordered.sort(QuantityArrangement::inOrderOfTheValues);

        List<Run> runs = new ArrayList<>();
        Parting under = null;
        for (Parting parting : ordered) {
            keep(space, runs, runBetween(under, parting, from, to));
            under = parting;
        }
        keep(space, runs, runBetween(under, null, from, to));
        return new QuantityArrangement(ordered, runs);
    }

    /** The run between two of the places the values part, held to what the rules leave either
     *  side. */
    private static Run runBetween(Parting under, Parting over, Bound from, Bound to) {
        // The places and not the lines against them go into the values. What a run asks a row for is
        // the same however many rules wrote a line where it stops, and which of them did is kept
        // beside it — carried in, it would be inside every value that says what is asked of a row.
        return new Run(
                new Band(Band.endAt(under == null ? null : under.geometry(), from, Towards.ABOVE),
                        Band.endAt(over == null ? null : over.geometry(), to, Towards.BELOW)),
                under, over);
    }

    /**
     * Which of two seams parts the values first.
     *
     * <p>Where the lines fall, and where two fall in one place, the one that gives that place away
     * before the one that keeps it. Two rules can part a carrier whose values fill at one number —
     * {@code <= 0.5} and {@code < 0.5} — and what they leave between them is that number and nothing
     * else. Ordered by a value either of them names, both name it, and one of the two readings put
     * the number in the runs on both sides of itself.
     *
     * <p>Asked of the line and not of the values beside it, because a line the quantity names no
     * value beside has none to be asked about.
     */
    private static int inOrderOfTheValues(Parting one, Parting other) {
        int where = one.geometry().at().compareTo(other.geometry().at());
        return where != 0 ? where : Boolean.compare(one.geometry().keepsItsOwnValueBelow(),
                other.geometry().keepsItsOwnValueBelow());
    }

    /**
     * The run just above {@code seam}, or null where the rules leave none there.
     *
     * <p>What the {@code IN} point of a border on the upper side asks for. Null is a run the rules
     * leave nothing in, which is a point nobody is owed a row at rather than one nothing has got
     * to.
     */
    public Run above(Parting parting) {
        return runs.stream().filter(each -> is(each.values().lower().seam(), parting)).findFirst()
                .orElse(null);
    }

    /** The run just below it, on the same reading. */
    public Run below(Parting parting) {
        return runs.stream().filter(each -> is(each.values().upper().seam(), parting)).findFirst()
                .orElse(null);
    }

    /**
     * The run at one end of what the rules leave: the one nothing parts below it, or nothing parts
     * above it.
     *
     * <p>What a bound bounds. A bound's line is where what it leaves stops, so the run it bounds is
     * the one against that end — and it is found by being the endmost rather than by holding the
     * line's own value, which a bound that stops short of that value does not leave in any run at
     * all. Null where the rules leave no run there, which is a point nobody is owed a row at.
     */
    public Run endmost(Towards inward) {
        return runs.stream()
                .filter(each -> (inward == Towards.ABOVE
                        ? each.values().lower() : each.values().upper()).seam() == null)
                .findFirst().orElse(null);
    }

    private static boolean is(Seam one, Parting other) {
        return one != null && other != null && one.key().equals(other.key());
    }

    /** A run, unless what the rules leave has nothing in it. */
    private static void keep(LevelSpace space, List<Run> runs, Run run) {
        Level first = run.values().first();
        Level last = run.values().last();
        if (first != null && last != null && space.compare(first, last) > 0) {
            return;
        }
        runs.add(run);
    }

    /**
     * Whether the rules leave nothing at the place this seam parts the values.
     *
     * <p>Asked of the place and not of the values either side of it. A line at the very edge of what
     * the rules leave has one of its two values outside them and parts what is left all the same —
     * read off that value, a bound's own line was dropped from the arrangement and the run it starts
     * belonged to no seam at all.
     */
    private static boolean outside(Seam seam, Bound from, Bound to) {
        return from != null && seam.at().compareTo(from.at()) < 0
                || to != null && seam.at().compareTo(to.at()) > 0;
    }
}
