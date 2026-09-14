package souther.compiler.partition;

import souther.compiler.numeric.EndSide;
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
     * @param below  what independently stops it at the low end. Never empty
     * @param above  the same at the high end
     */
    public record Run(Band values, List<RegionClaim> below, List<RegionClaim> above) {

        public Run {
            if (values == null) {
                throw new IllegalArgumentException("a run is a run of values");
            }
            below = List.copyOf(below);
            above = List.copyOf(above);
            agree(values.lower(), below, EndSide.LOWER);
            agree(values.upper(), above, EndSide.UPPER);
        }

        /**
         * That the run and what stops it say the same thing about one end.
         *
         * <p>Checked rather than trusted, because this is the answer about what stops a run and a
         * value saying one thing in its geometry and another in its claims would be two answers to
         * the question it exists to settle. Every claim is held to where the run actually reaches:
         * a line is what stops it only where the run gets to that line, and an end the rules leave
         * only where the run gets to that end — which is the whole of what the two have to agree
         * about, and checking less than that left a run reaching one place and claiming to be
         * stopped at another.
         *
         * @param side which end of the run this is, so that the run lies the other way from it
         */
        private static void agree(BandEnd end, List<RegionClaim> claims, EndSide side) {
            if (claims.isEmpty()) {
                throw new IllegalArgumentException(
                        "a run stops at its " + side + " end because something stops it");
            }
            Bound reaches = end.reaches();
            if (reaches == null) {
                if (!claims.equals(List.of(new RegionClaim(
                        new FarEnd.AtTheOrderEnd(side.outward()), PointContributions.none())))) {
                    throw new IllegalArgumentException("a run nothing stops at its " + side
                            + " end, stopped by " + claims);
                }
                return;
            }
            for (RegionClaim claim : claims) {
                Bound at = switch (claim.basis()) {
                    case FarEnd.AtALine line -> Band.atTheLine(line.where(), side.inward());
                    case FarEnd.AtTheDomain domain -> domain.reaches();
                    case FarEnd.AtTheOrderEnd _ -> null;
                };
                if (at == null || !at.canonical().equals(reaches.canonical())) {
                    throw new IllegalArgumentException("a run reaching " + reaches + " at its "
                            + side + " end, claimed to be stopped at " + claim.basis());
                }
            }
        }

        /**
         * What a row inside this run is owed to at one end: one answer per thing that stops it
         * there on its own.
         *
         * <p>Worked out where the run was built, which is the one place holding everything that goes
         * into it. A line at the end and the end the rules leave are two answers to one question and
         * either can be the tighter, so which of them the run actually stops at is not something the
         * shape of the end says — and a reader that took the line because there was one wrote down a
         * rule that is not what settles the region.
         */
        public List<RegionClaim> endsAt(Towards side) {
            return side == Towards.ABOVE ? above : below;
        }
    }

    /**
     * What stops a run at one end, one answer per thing that does it on its own.
     *
     * <p>A line the model wrote and the end every rule leaves together can fall in one place, and
     * then each of them stops the run there without the other: taking either away leaves it where it
     * is, so a row inside is owed for both. Where they fall apart, only the tighter stops it, and the
     * other is a line the run never reaches — writing that one down would name a rule that does not
     * settle the region, and two readings whose regions differ would come back as one point.
     *
     * <p>Compared as places rather than as they are written, so that two spellings of one end are
     * one end ({@link Bound#canonical()}).
     *
     * @param side which end of the run this is, which the run lies inward of
     */
    private static List<RegionClaim> stoppedBy(BandEnd end, Parting parted, DomainEnd leaves,
                                               EndSide side) {
        Bound reaches = end.reaches();
        if (reaches == null) {
            return List.of(new RegionClaim(
                    new FarEnd.AtTheOrderEnd(side.outward()), PointContributions.none()));
        }
        List<RegionClaim> out = new ArrayList<>();
        if (parted != null
                && Band.atTheLine(parted.geometry(), side.inward()).canonical().equals(
                        reaches.canonical())) {
            parted.alternatives().forEach(line -> out.add(new RegionClaim(
                    new FarEnd.AtALine(line, parted.geometry()), PointContributions.by(line))));
        }
        // The end of the rules and the place the run gets to, which are two answers about two
        // layers: the attribution came matched to where the reading left the quantity, and this asks
        // whether the run stops at the value that end lowers onto. Both have to hold before a name
        // is written, and neither is the other's answer — so the names are read here and not where
        // the end was lowered.
        if (leaves != null && leaves.bound().canonical().equals(reaches.canonical())) {
            out.add(new RegionClaim(new FarEnd.AtTheDomain(leaves.bound()),
                    PointContributions.byNarrowing(leaves)));
        }
        if (out.isEmpty()) {
            // Where the run reaches is the tighter of the two, so one of them is it. Reaching here
            // is this reading and the one that built the run disagreeing about where it stops.
            throw new IllegalStateException("a run reaching " + reaches
                    + " that neither the line beside it nor the end the rules leave stops there: "
                    + parted + " / " + leaves);
        }
        return RegionClaim.byBasis(out);
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
        return of(space, parted, DomainEnds.NONE);
    }


    /**
     * The same, where the rules leave the quantity only what runs between {@code ends}.
     *
     * <p>The ends are not seams and never become runs of their own. Nothing outside a bound can be
     * constructed, so there is no run on the far side of one to cover (ADR-0090); what a bound does
     * is stop the run beside it, which is why the two either side of a line at ten run from the
     * bound rather than from the order's own extent.
     *
     * @param ends where the rules leave off either way and whether they keep the place they leave
     *             off at, each under the side it is. Not the first value in the run: a strict bound
     *             on a carrier with no step leaves no first value, and read as one such a run either
     *             had no end at all or held the value its bound refuses. Taken as one value rather
     *             than as two arguments so that which end is which is not said again here
     */
    public static QuantityArrangement of(LevelSpace space, List<Parting> parted, DomainEnds ends) {
        Map<String, Parting> distinct = new LinkedHashMap<>();
        for (Parting each : parted) {
            // A place the rules leave nothing at divides nothing. The values it would tell apart are
            // values no row can be written at, so it is dropped rather than kept as a run holding
            // none — which is a class an author would be told to write a row for and could not.
            if (outside(each.geometry(), ends.boundAt(EndSide.LOWER),
                    ends.boundAt(EndSide.UPPER))) {
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
            keep(space, runs, runBetween(under, parting, ends));
            under = parting;
        }
        keep(space, runs, runBetween(under, null, ends));
        return new QuantityArrangement(ordered, runs);
    }

    /** The run between two of the places the values part, held to what the rules leave either
     *  side. */
    private static Run runBetween(Parting under, Parting over, DomainEnds ends) {
        // The places and not the lines against them go into the values. What a run asks a row for is
        // the same however many rules wrote a line where it stops, and which of them did is kept
        // beside it — carried in, it would be inside every value that says what is asked of a row.
        BandEnd lower = Band.endAt(under == null ? null : under.geometry(),
                ends.boundAt(EndSide.LOWER), EndSide.LOWER.inward());
        BandEnd upper = Band.endAt(over == null ? null : over.geometry(),
                ends.boundAt(EndSide.UPPER), EndSide.UPPER.inward());
        return new Run(new Band(lower, upper),
                stoppedBy(lower, under, ends.at(EndSide.LOWER), EndSide.LOWER),
                stoppedBy(upper, over, ends.at(EndSide.UPPER), EndSide.UPPER));
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
     * The run on one side of a line, given every place that line parts the values.
     *
     * <p>Asked with the side and never with a place picked out of the list. How many places a line
     * parts the values at is what kind of rule drew it — one where it orders them, two where it
     * names a value and leaves the run under it and the run over it — and that is topology, which
     * is this arrangement's and not a reader's. A caller choosing between them is a caller that has
     * to know how many there are, and gets it wrong the day a third shape of rule is written.
     *
     * @param parted every place this line parts the values, in any order
     */
    public Run beside(java.util.Collection<Parting> parted, Towards side) {
        // The run this side of every place the line parts them, which is the one this line does not
        // also bound at its far end. A rule that names a value leaves the value itself between its
        // two places, and that run is on neither side of the line: it is the line.
        for (Parting each : parted) {
            Run run = side == Towards.ABOVE ? above(each) : below(each);
            if (run == null) {
                continue;
            }
            BandEnd far = side == Towards.ABOVE ? run.values().upper() : run.values().lower();
            boolean ourOwn = far.seam() != null
                    && parted.stream().anyMatch(also -> is(far.seam(), also));
            if (!ourOwn) {
                return run;
            }
        }
        return null;
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
        return (from != null && seam.at().compareTo(from.at()) < 0)
                || (to != null && seam.at().compareTo(to.at()) > 0);
    }
}
