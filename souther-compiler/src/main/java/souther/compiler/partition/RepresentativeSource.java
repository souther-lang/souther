package souther.compiler.partition;

import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeReachName;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * How a value standing for one equivalence class is arrived at: take these values, compose one this
 * way, or report that there is none.
 *
 * <p>A recipe rather than a list of values, because the ways of arriving at one are not the same
 * kind of thing. Some classes name their values outright. A class whose values are records names
 * the constructor instead — a record's fields are chosen one at a time against the rules relating
 * them, which is the generator's walk and not a list anything here could hold.
 *
 * <p>A value at a position written under a name is that value with the name put back on, and a
 * name can be put on a value that does not exist yet: a class of {@code DecisionN} that composes an
 * {@code Approved} is a row of {@code DecisionN(Approved { id = 1 })}, decided before anything has
 * composed the {@code Approved}. So the names are part of what a composition carries, and go on
 * when the value is made. Held as an empty list of values with an optional constructor beside it,
 * the names would have nowhere to be, and what reached a row declaring {@code DecisionN} would be an
 * {@code Approved} — which is not a value of it.
 *
 * <p>Held in the one form a reader acts on. Putting names on a recipe is worked out where it is done
 * ({@link #under(List, RepresentativeSource)}) and not kept as a recipe over a recipe, so what a
 * class holds says what to do and nothing about how it was put together: two classes that come to
 * the same thing are equal, and a reader has four cases to answer and none to read through.
 *
 * <p>More than one value, where there are values, because building a candidate can fail for a
 * reason that is about the combination and not about the class: two classes each covering a wide
 * range, whose chosen representatives happen to break a constraint that relates them. A generator
 * that held one value per class would call that combination impossible when another value would
 * have built.
 */
public sealed interface RepresentativeSource {

    /** Values ready to be written at the position, in the order to try them, under every name it
     *  wears. Never empty: a class with nothing to write is {@link NothingProducible}, which says
     *  why. */
    record Values(List<FixtureTemplate> written) implements RepresentativeSource {

        public Values {
            written = List.copyOf(written);
            if (written.isEmpty()) {
                throw new IllegalArgumentException(
                        "no values is `NothingProducible`, which says why");
            }
        }
    }

    /**
     * A value composed through {@code through}, field by field, and written under {@code worn}.
     *
     * <p>{@code through} is not the position's type: the declared type is still the sum, and only
     * the value being built is narrowed. {@code worn} is what the position writes that value under,
     * outermost first — a fact about the position rather than about the constructor.
     */
    record Compose(TypeSymbol.AtModule through, List<TypeReachName.Written> worn)
            implements RepresentativeSource {

        public Compose {
            worn = List.copyOf(worn);
        }

        /** What was composed, under the names the position writes it under. */
        public FixtureTemplate written(FixtureTemplate composed) {
            return under(worn, composed);
        }
    }

    /**
     * Nothing can produce a value for this class, and why.
     *
     * <p>What the class knows about itself. A reader told only that there are no values would
     * report a case somebody can write in one line as a row that does not exist.
     */
    record NothingProducible(String why) implements RepresentativeSource {}

    /**
     * Nothing was produced for this class and nothing here says none can be.
     *
     * <p>Apart from {@link NothingProducible}, and the difference is what a reader may say about the
     * model. That one is a search that looked everywhere it was going to look; this one stopped — at
     * a figure of this compiler's, or short of a population it writes some of — so the class may
     * hold values and this did not reach one.
     *
     * <p>Run together, the sentence an author reads says nothing writes a value in a range whose
     * values this compiler simply did not walk to. Which is the same mistake as reporting a
     * compiler's own shortfall in words about the model, one layer up from where it was fixed.
     *
     * @param heldBack which figures of this compiler's stopped it, each a number somebody can raise
     *                 to have the search go on
     * @param notAllOf what it wrote some of rather than all of, which no figure reaches
     * @param why      what to tell a reader, in words that are about this compiler
     */
    record NotArrivedAt(Set<CompositionBudget> heldBack, Set<CompositionRepertoire> notAllOf,
                        String why) implements RepresentativeSource {

        public NotArrivedAt {
            heldBack = Set.copyOf(heldBack);
            notAllOf = Set.copyOf(notAllOf);
            if (heldBack.isEmpty() && notAllOf.isEmpty()) {
                // Nothing stopped it and it reached nothing, which is a search that looked
                // everywhere — and that is the other case, which says so.
                throw new IllegalArgumentException(
                        "a class nothing reached a value for says what stopped the reaching: "
                                + why);
            }
        }
    }

    /**
     * Whether a value of this class can be produced at all.
     *
     * <p>Not whether there are values here: a class composed through a constructor has none and is
     * produced all the same. That is a fact about generation either way, and never about the class
     * — the class is still counted, and rows that already reach it still count.
     */
    default boolean buildable() {
        return switch (this) {
            case Values _, Compose _ -> true;
            // And a class nothing reached a value for is not one a caller may count on either. What
            // this answers is whether a value can be had, and a search that stopped has not said.
            case NothingProducible _, NotArrivedAt _ -> false;
        };
    }

    static RepresentativeSource of(FixtureTemplate... values) {
        return new Values(List.of(values));
    }

    static RepresentativeSource of(List<FixtureTemplate> values) {
        return new Values(values);
    }

    /**
     * {@code source}, written under {@code wrappers}, outermost first.
     *
     * <p>A newtype is the value it wraps, so what a position divides into is read through the names
     * — and what a row writes is the value with those names back on. Both directions are the same
     * fact, which is why this is one operation rather than spelled by whoever happened to need it: a
     * class of {@code data StageN = Stage} offers {@code StageN(Prospecting)} and a class of
     * {@code data DecisionN = Decision} composes an {@code Approved} and hands back
     * {@code DecisionN(Approved { id = 1 })}, by one rule.
     */
    static RepresentativeSource under(List<TypeReachName.Written> wrappers,
                                      RepresentativeSource source) {
        if (wrappers.isEmpty()) {
            return source;
        }
        return switch (source) {
            case Values values -> new Values(
                    values.written().stream().map(each -> under(wrappers, each)).toList());
            // The names go on outside whatever the composition already wears, which is the order
            // they were read off the position in.
            case Compose compose -> {
                List<TypeReachName.Written> both = new ArrayList<>(wrappers);
                both.addAll(compose.worn());
                yield new Compose(compose.through(), both);
            }
            // Nothing to put a name on. What the class says stands: a name wrapped round a value
            // nothing composed does not make one, and does not change why there is none — nor
            // whether anything looked.
            case NothingProducible _, NotArrivedAt _ -> source;
        };
    }

    /**
     * A value under the names it is written with, outermost first.
     *
     * <p>The one spelling of putting them back on. What a row writes and what a value composed
     * later is written as are the same operation, and two spellings of it are two chances to
     * disagree about which name goes outside.
     */
    static FixtureTemplate under(List<TypeReachName.Written> worn, FixtureTemplate value) {
        FixtureTemplate at = value;
        // Innermost last: the names were read off the position outermost first, so they go back on
        // in the order that leaves the outermost outside.
        for (int i = worn.size() - 1; i >= 0; i--) {
            at = FixtureTemplate.newtype(worn.get(i), at);
        }
        return at;
    }
}
