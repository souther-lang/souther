package souther.compiler.partition;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;

/**
 * Values put forward for a position, in the order a caller reaches for them, and where in that
 * order a figure of this compiler's stopped a value from being built.
 *
 * <p>Two halves of one answer. A builder stopped by a figure — a list longer than a proposal holds,
 * more pairings than are built at once — hands back fewer values than the type has, and a reader
 * holding the values alone reads that as the type having no more: a set of two of a newtype over a
 * long list read as one nothing can build, where it is one this compiler declined to build.
 *
 * <p><b>Where it stopped, and not only that it did.</b> A caller takes the first few values and
 * leaves the rest, and whether a stop is part of its answer turns on which side of what it took
 * the stop stands. A stop in front of a value taken is a value that would have been taken in its
 * place, so it is the caller's; a stop past the last value taken is a value nobody would have
 * reached. Kept on the list as a whole, one of the two is said wrongly whichever way the list
 * decides — so the stop is kept where it happened, and the caller that knows how far it went asks
 * for that much ({@link #firstOf}).
 *
 * <p>Nor is it a verdict: values built beside a stop are values, and a row composed of them is a
 * row whatever stopped the others. Which of the two a reader is owed is decided where the search
 * comes back ({@link Generator}), not here.
 *
 * @param entries the values and the stops, in the order the build came to them
 */
record Proposals(List<Entry> entries) {

    /** One place in the order: a value, or a value a figure kept from being built. */
    sealed interface Entry {}

    /** A value built. */
    record Offered(FixtureTemplate value) implements Entry {

        public Offered {
            Objects.requireNonNull(value, "a value offered is a value");
        }
    }

    /** A value not built there, and what of this compiler's stopped it. */
    record Stopped(CompositionShortfall met) implements Entry {

        public Stopped {
            if (met.nothing()) {
                throw new IllegalArgumentException("a stop says what stopped it");
            }
        }
    }

    /** Nothing built, and nothing stopped it. */
    static final Proposals NONE = new Proposals(List.of());

    Proposals {
        entries = List.copyOf(entries);
    }

    /** These, built with nothing of this compiler's stopping the build. */
    static Proposals of(List<FixtureTemplate> values) {
        Gathering out = Gathering.inOrder();
        values.forEach(out::add);
        return out.done();
    }

    /** {@code value} alone, or nothing where there is none, with nothing stopping the build. */
    static Proposals ofNullable(FixtureTemplate value) {
        return value == null ? NONE : of(List.of(value));
    }

    /** Nothing, because {@code figure} stopped it. */
    static Proposals stoppedBy(CompositionBudget figure) {
        return new Proposals(List.of(new Stopped(CompositionShortfall.of(List.of(figure)))));
    }

    /**
     * The same, as built having met {@code more} before any of it: what was met in building these
     * values themselves, which every caller taking one of them takes with it.
     */
    Proposals meeting(CompositionShortfall more) {
        if (more.nothing()) {
            return this;
        }
        List<Entry> out = new ArrayList<>();
        out.add(new Stopped(more));
        out.addAll(entries);
        return new Proposals(out);
    }

    /** The values, in order. */
    List<FixtureTemplate> values() {
        List<FixtureTemplate> out = new ArrayList<>();
        for (Entry each : entries) {
            if (each instanceof Offered(FixtureTemplate value)) {
                out.add(value);
            }
        }
        return List.copyOf(out);
    }

    /** Every stop there is, which is what a caller taking all of it met. */
    CompositionShortfall met() {
        CompositionShortfall out = CompositionShortfall.NONE;
        for (Entry each : entries) {
            if (each instanceof Stopped(CompositionShortfall met)) {
                out = out.and(met);
            }
        }
        return out;
    }

    boolean isEmpty() {
        return entries.stream().noneMatch(Offered.class::isInstance);
    }

    /**
     * What a caller taking the first {@code many} values reached: those values, and every stop in
     * front of the last of them — and, where there are fewer, every stop there is, since the caller
     * went to the end looking for more.
     */
    Proposals firstOf(int many) {
        List<Entry> out = new ArrayList<>();
        int taken = 0;
        for (Entry each : entries) {
            if (taken >= many) {
                break;
            }
            out.add(each);
            if (each instanceof Offered) {
                taken++;
            }
        }
        return new Proposals(out);
    }

    /** The same order with each value put through {@code written}, leaving out a value it makes
     *  nothing of; the stops stand where they stood. */
    Proposals map(Function<FixtureTemplate, FixtureTemplate> written) {
        Gathering out = Gathering.inOrder();
        for (Entry each : entries) {
            switch (each) {
                case Offered(FixtureTemplate value) -> {
                    FixtureTemplate made = written.apply(value);
                    if (made != null) {
                        out.add(made);
                    }
                }
                case Stopped(CompositionShortfall met) -> out.stop(met);
            }
        }
        return out.done();
    }

    /**
     * An order being put together: values and stops appended as a build comes to them.
     *
     * <p>Where a stop stands is where it was appended, so a value left out as one already there
     * leaves the stops either side of it in place.
     */
    static final class Gathering {

        private final List<Entry> entries = new ArrayList<>();

        /** The texts written so far, where a value written twice is one; null where it is two. */
        private final Set<String> written;

        private int size;

        private Gathering(Set<String> written) {
            this.written = written;
        }

        /** Each value once, by how it is written. */
        static Gathering distinct() {
            return new Gathering(new HashSet<>());
        }

        /** Every value as it comes. */
        static Gathering inOrder() {
            return new Gathering(null);
        }

        /** {@code value} appended, unless it is one already here; whether it was. */
        boolean add(FixtureTemplate value) {
            if (written != null && !written.add(value.text())) {
                return false;
            }
            entries.add(new Offered(value));
            size++;
            return true;
        }

        /** A value not built here, for what {@code met} says; nothing where it says nothing. */
        void stop(CompositionShortfall met) {
            if (!met.nothing()) {
                entries.add(new Stopped(met));
            }
        }

        /** Every entry of {@code more}, in its order. */
        void addAll(Proposals more) {
            addAll(more, Integer.MAX_VALUE);
        }

        /** The entries of {@code more} in its order until this holds {@code many} values: what a
         *  walk asking for that many reaches. */
        void addAll(Proposals more, int many) {
            for (Entry each : more.entries()) {
                if (size >= many) {
                    return;
                }
                switch (each) {
                    case Offered(FixtureTemplate value) -> add(value);
                    case Stopped(CompositionShortfall met) -> stop(met);
                }
            }
        }

        /** How many values are here. */
        int size() {
            return size;
        }

        Proposals done() {
            return new Proposals(entries);
        }
    }
}
