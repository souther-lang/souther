package souther.compiler.partition;

import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.List;

/**
 * How a value standing for one equivalence class is arrived at.
 *
 * <p>A recipe rather than a list of values, because the ways of arriving at one are not the same
 * kind of thing. Some classes name their values outright. A class whose values are records names
 * the constructor instead — a record's fields are chosen one at a time against the rules relating
 * them, which is the generator's walk and not a list anything here could hold. And a value at a
 * position written under a name is that value with the name put back on, which is neither of the
 * first two but a projection over one of them.
 *
 * <p>The projection is why this is an algebra and not a list with two things beside it. A name can
 * be put on a value that does not exist yet: {@code Composed(Approved)} under {@code DecisionN} is
 * a row of {@code DecisionN(Approved { id = 1 })}, decided before anything has composed the
 * {@code Approved}. Held as an empty list of values with an optional constructor beside it, the
 * names had nowhere to be at all, and what reached a row declaring {@code DecisionN} was an
 * {@code Approved} — which is not a value of it.
 *
 * <p>More than one value, where there are values, because building a candidate can fail for a
 * reason that is about the combination and not about the class: two classes each covering a wide
 * range, whose chosen representatives happen to break a constraint that relates them. A generator
 * that held one value per class would call that combination impossible when another value would
 * have built.
 */
public sealed interface RepresentativeSource {

    /**
     * What arriving at a value of this class comes to, with every name the position wears already
     * taken into account.
     *
     * <p>One closed answer, and what a reader deciding what to do reads. The cases of this interface
     * are how a recipe is <em>written</em> — a projection sits over another recipe, and reading it
     * means reading what is under it — whereas an {@link Evaluation} is what a reader has to
     * <em>do</em>, and the two are not the same set of things. A reader that asked "is there a
     * constructor", "are there values", "was a reason given" separately would be recovering the
     * variant from three answers, and could meet combinations no recipe can be in.
     */
    Evaluation evaluate();

    /**
     * What a reader does about one class: take these values, compose one this way, or report that
     * there is none.
     *
     * <p>Closed and flat. A projection is not a case here because it is not something to do — it is
     * accounted for in what the other cases carry, which is what makes putting the names back on
     * the one thing it is.
     */
    sealed interface Evaluation {

        /** Values ready to be written at the position, in the order to try them, under every name
         *  it wears. Never empty: a class with nothing to write is {@link NothingProducible}. */
        record Values(List<FixtureTemplate> written) implements Evaluation {

            public Values {
                written = List.copyOf(written);
                if (written.isEmpty()) {
                    throw new IllegalArgumentException(
                            "no values is `NothingProducible`, which says why");
                }
            }
        }

        /**
         * A value composed through {@code through}, field by field, and written under
         * {@code worn}.
         *
         * <p>{@code through} is not the position's type: the declared type is still the sum, and
         * only the value being built is narrowed. {@code worn} is what the position writes that
         * value under, outermost first — a fact about the position rather than about the
         * constructor.
         */
        record Compose(TypeName through, List<TypeName> worn) implements Evaluation {

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
        record NothingProducible(String why) implements Evaluation {}
    }

    /**
     * Whether a value of this class can be produced at all.
     *
     * <p>Not whether there are values here: a class composed through a constructor has none and is
     * produced all the same. That is a fact about generation either way, and never about the class
     * — the class is still counted, and rows that already reach it still count.
     */
    default boolean buildable() {
        return switch (evaluate()) {
            case Evaluation.Values _, Evaluation.Compose _ -> true;
            case Evaluation.NothingProducible _ -> false;
        };
    }

    /**
     * Values named outright, and at least one of them.
     *
     * <p>Empty used to be allowed and meant a class nothing produced a value for and nothing said
     * why. Nothing wrote one — every producer already branched to {@link Ungeneratable} where its
     * values ran out — and what the state bought was a reader with a fourth answer to give, which
     * it gave as the position having no value. A class that cannot produce one says why.
     */
    record Ready(List<FixtureTemplate> values) implements RepresentativeSource {

        public Ready {
            values = List.copyOf(values);
            if (values.isEmpty()) {
                throw new IllegalArgumentException(
                        "a class with no values is `Ungeneratable`, which says why");
            }
        }

        @Override
        public Evaluation evaluate() {
            return new Evaluation.Values(values);
        }
    }

    /** A class whose values are composed through {@code through}, field by field, by the walk that
     *  composes every other record. */
    record Composed(TypeName through) implements RepresentativeSource {

        @Override
        public Evaluation evaluate() {
            return new Evaluation.Compose(through, List.of());
        }
    }

    /**
     * The same recipe, written under the names the position wears, outermost first.
     *
     * <p>A newtype is the value it wraps, so what a position divides into is read through the names
     * — and what a row writes is the value with those names back on. Both directions are the same
     * fact, which is why the projection sits over the recipe rather than being spelled by whoever
     * happened to need it: a class of {@code data StageN = Stage} offers {@code StageN(Prospecting)}
     * and a class of {@code data DecisionN = Decision} composes an {@code Approved} and hands back
     * {@code DecisionN(Approved { id = 1 })}, by one rule.
     */
    record Projected(RepresentativeSource inner, List<TypeName> wrappers)
            implements RepresentativeSource {

        public Projected {
            wrappers = List.copyOf(wrappers);
        }

        @Override
        public Evaluation evaluate() {
            return switch (inner.evaluate()) {
                case Evaluation.Values values -> new Evaluation.Values(
                        values.written().stream().map(each -> under(wrappers, each)).toList());
                // The names go on outside whatever the inner recipe already wears, which is the
                // order they were read off the position in.
                case Evaluation.Compose compose -> {
                    List<TypeName> both = new ArrayList<>(wrappers);
                    both.addAll(compose.worn());
                    yield new Evaluation.Compose(compose.through(), both);
                }
                // Nothing to put a name on. What the inner recipe says stands: a name wrapped round
                // a value nothing composed does not make one, and does not change why there is none.
                case Evaluation.NothingProducible _ -> inner.evaluate();
            };
        }
    }

    /** A class nothing can produce a value for, and why. */
    record Ungeneratable(String why) implements RepresentativeSource {

        @Override
        public Evaluation evaluate() {
            return new Evaluation.NothingProducible(why);
        }
    }

    static RepresentativeSource of(FixtureTemplate... values) {
        return new Ready(List.of(values));
    }

    static RepresentativeSource of(List<FixtureTemplate> values) {
        return new Ready(values);
    }

    /** {@code inner}, written under {@code wrappers} — or {@code inner} itself where the position
     *  wears no name, so that a recipe carries no projection over nothing. */
    static RepresentativeSource under(List<TypeName> wrappers, RepresentativeSource inner) {
        return wrappers.isEmpty() ? inner : new Projected(inner, wrappers);
    }

    /**
     * A value under the names it is written with, outermost first.
     *
     * <p>The one spelling of putting them back on. What a row writes and what a value composed
     * later is written as are the same operation, and two spellings of it are two chances to
     * disagree about which name goes outside.
     */
    static FixtureTemplate under(List<TypeName> worn, FixtureTemplate value) {
        FixtureTemplate at = value;
        // Innermost last: the names were read off the position outermost first, so they go back on
        // in the order that leaves the outermost outside.
        for (int i = worn.size() - 1; i >= 0; i--) {
            at = FixtureTemplate.newtype(worn.get(i), at);
        }
        return at;
    }
}
