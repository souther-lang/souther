package souther.compiler.check;

import souther.compiler.types.Denotation;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/**
 * What the names written in a module mean, asked one question at a time.
 *
 * <p>The operations {@link TypeScope} performs on a module's meanings, and nothing else. Not a table
 * and not a way of getting one: a reader handed the table decides for itself when to fetch it, and
 * where the table is an answer of a query store that decision is what an edit costs — a reader that
 * fetches to build a scope has depended on every name in the module before reading one of them.
 * Kept as operations, where the meanings come from is the implementation's, and a reader cannot tell
 * a table it was handed from one asked for as it is read.
 *
 * <p>Which is what lets the fetching get finer without a reader changing. {@link #of} is a question
 * about one spelling and {@link #spellings} is the one that is genuinely about all of them, so a
 * store-backed implementation asking for a module's meanings on first read can become one asking
 * for a spelling at a time, and nothing above here is written in terms of either.
 *
 * <p>Absence is not one of the answers. A module this compilation does not have is a module in
 * which every spelling means nothing, which is what {@link #NONE} says — so nothing that reads a
 * scope has to know that a compilation can be missing a module.
 */
public interface Denoting {

    /** What {@code spelling} means here — {@link Denotation.NotInScope} where nothing here is
     * written that way. */
    Denotation of(String spelling);

    /** Every spelling written here, which is what a reader offering what a mistyped name may have
     * meant has to have all of. A spelling standing for nothing is one of these; what it means is
     * {@link #of}'s answer and a second question. */
    Set<String> spellings();

    /** The module an {@code import ... as} alias reaches, or null where no alias here does. */
    String moduleOfAlias(String alias);

    /** Every alias written here. */
    Set<String> aliases();

    /** Nothing is written here: the meanings of a module no compilation has, and of a signature
     * written over primitives and type variables alone. */
    Denoting NONE = of(Map.of(), Map.of());

    /**
     * The meanings a caller already holds.
     *
     * <p>What every reader outside a query store is answered from, and what a store-backed one
     * answers from once it has asked. A {@link Denotation.NotInScope} is refused rather than kept:
     * that is the answer for a spelling with no entry, so an entry holding it would be a spelling
     * written here that is also not, and {@link #of} could not say which — which is the one way the
     * table and the operations could come apart.
     */
    static Denoting of(Map<String, Denotation> denotations, Map<String, String> aliases) {
        Map<String, Denotation> names =
                Collections.unmodifiableMap(new LinkedHashMap<>(denotations));
        Map<String, String> reached =
                Collections.unmodifiableMap(new LinkedHashMap<>(aliases));
        names.forEach((spelling, denotation) -> {
            if (denotation instanceof Denotation.NotInScope) {
                throw new IllegalArgumentException("`" + spelling + "` would be written here and "
                        + "not written here: NotInScope is what a spelling with no entry means");
            }
        });
        return new Denoting() {
            @Override
            public Denotation of(String spelling) {
                Denotation denotation = names.get(spelling);
                return denotation == null ? Denotation.NOT_IN_SCOPE : denotation;
            }

            @Override
            public Set<String> spellings() {
                return names.keySet();
            }

            @Override
            public String moduleOfAlias(String alias) {
                return reached.get(alias);
            }

            @Override
            public Set<String> aliases() {
                return reached.keySet();
            }
        };
    }
}
