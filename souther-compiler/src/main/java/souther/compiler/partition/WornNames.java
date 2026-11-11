package souther.compiler.partition;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.TypeView;
import souther.compiler.diag.msg.SearchMessage;
import souther.compiler.types.TypeReachName;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;

/**
 * How this module writes the names a position wears, or the one of them it cannot write.
 *
 * <p>Asked before anything is written under them, and answered for all of them at once. The name
 * goes on the value as the value is written, so a name this module cannot reach is not a value
 * written without that name — it is no value here at all, and every name has to be in hand before
 * the first one goes on. A reading that put them on as it resolved them would leave a value wearing
 * some of its names when the next one turned out to have no spelling.
 *
 * <p>Which one it was, and not that there was one. A reader told only that the names could not be
 * written has to find out for itself which name and why, and each of them finds a different way of
 * saying it — so the name that stopped this is carried, and the sentence about it is written here
 * where the question was asked.
 */
sealed interface WornNames {

    /** Every name the position wears, spelled as this module reaches it, outermost first. */
    record Spelled(List<TypeReachName.Written> names) implements WornNames {

        public Spelled {
            names = List.copyOf(names);
        }

        /** A collection holding {@code elements}, under these names. */
        FixtureTemplate holding(List<FixtureTemplate> elements) {
            return RepresentativeSource.under(names, FixtureTemplate.collection(elements));
        }
    }

    /** A name nothing here can write, which takes the whole value with it. */
    record Unwritable(TypeSymbol name) implements WornNames {

        SearchMessage why() {
            return noSpellingFor(name);
        }
    }

    /** How {@code worn} is written here, outermost first, or the first of them that has no
     *  spelling. */
    static WornNames of(List<TypeSymbol> worn, RuleReadingSource ruleSource) {
        List<TypeReachName.Written> names = new ArrayList<>();
        for (TypeSymbol wears : worn) {
            if (!(ruleSource.symbols().scope().reach(wears)
                    instanceof TypeReachName.Written written)) {
                return new Unwritable(wears);
            }
            names.add(written);
        }
        return new Spelled(names);
    }

    /**
     * {@code value} under {@code worn}, or null where one of those names cannot be written here.
     *
     * <p>Null takes the whole value with it: the name goes on the value as it is written, and a
     * value written without one is of a type the position does not declare. What comes back is
     * {@code value} itself where the position wears no name, so that nothing is written round
     * nothing.
     *
     * <p>The names are the reading's. Nothing here works out which names a value wears — that is
     * what reading the position came to — and the putting-back-on is
     * {@link RepresentativeSource#under}'s, so a value never wears a name that was spelled anywhere
     * but here.
     */
    static FixtureTemplate under(List<TypeSymbol> worn, FixtureTemplate value,
                                 RuleReadingSource ruleSource) {
        if (value == null || worn.isEmpty()) {
            return value;
        }
        return of(worn, ruleSource) instanceof Spelled spelled
                ? RepresentativeSource.under(spelled.names(), value) : null;
    }

    /**
     * A collection holding {@code elements}, under the names {@code container} wears — or null
     * where a name it wears cannot be written.
     *
     * <p>The one place a collection is put on the names of its type: a list a newtype wraps is
     * written as that newtype and not as the bare list, which a boundary reading the position
     * refuses, so every reader that makes a collection of a position's type makes it here. A
     * reader that makes many asks {@link #of} once and holds on to the {@link Spelled}: whether
     * the names can be written is a fact of the type, so a type whose names cannot be is known
     * before the first collection is made and not after every one of them came back null.
     */
    static FixtureTemplate collectionHolding(TypeView container, List<FixtureTemplate> elements,
                                             RuleReadingSource ruleSource) {
        return of(container.wrappers(), ruleSource) instanceof Spelled spelled
                ? spelled.holding(elements) : null;
    }

    /** Why nothing here can write a value of {@code name}: no spelling reaches it. */
    static SearchMessage noSpellingFor(TypeSymbol name) {
        return name instanceof TypeSymbol.AtModule at
                ? new SearchMessage.TheModuleDoesNotExposeIt(String.valueOf(at.module()),
                        String.valueOf(at.name()))
                // What the language declares is kept by nobody: a declaration of this module
                // spells it, so the language's has no name left here.
                : new SearchMessage.TheNameIsDeclaredHere(String.valueOf(name.name()));
    }
}
