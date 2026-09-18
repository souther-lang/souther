package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Whether the spreads of a product reach a declaration they are written on.
 *
 * <p>A value of a product holds the fields of everything it spreads, so a declaration that spreads
 * its way back to itself is one made of itself: there is no value of it, and nothing that works out
 * what it holds has anything to stop at. Every walk over the spreads would run until the stack did.
 *
 * <p><b>Asked of the declarations and not of a walk.</b> What each walk below does about a back edge
 * is that walk's own business and says nothing about the language — {@link FieldExpansion} hands one
 * back so that an expansion is finite, which is a way of not running forever and not a rule anybody
 * wrote. The rule is here, answered once from the declarations alone, and what is downstream of it
 * reads a graph this has been over.
 *
 * <p><b>On the path, not reached before.</b> A declaration two spreads of one graph reach is reached
 * twice and is no cycle: the two fields it brings in are two fields with one name, which is a field
 * collision and stays one. What closes a ring is a spread reaching a declaration the walk is
 * currently inside, so the three states a depth-first walk has are all three needed — never reached,
 * on the path, and done with.
 */
public final class ProductSpreads {

    private ProductSpreads() {}

    /** Where a declaration is read from — as {@link FieldExpansion.Declarations}, and separate from
     *  it because what is read here is the graph and never a field of it. */
    @FunctionalInterface
    public interface Declarations {

        /** The declaration at {@code named} with its names resolved, or null where none is. */
        Hir.Def at(TypeSymbol.AtModule named);
    }

    /** What the declarations handed over came to. */
    public sealed interface Of {}

    /**
     * No spread of any of them reaches a declaration it is written under.
     *
     * <p>What it carries is every declaration the walk went over: the ones it was handed, and every
     * one their spreads reach. A reader below takes the answer rather than the fact that a check
     * ran, so that what it is about to walk is something this names. A declaration no field can be
     * taken out of is here too, having been gone over and having nothing to spread.
     *
     * <p>A set, because that is what it is. Which order the walk reached them in is the walk's and
     * belongs to nothing here — carried as a sequence, an edit that only moved a declaration would
     * come back as a different answer.
     */
    public record WellFounded(Set<TypeSymbol.AtModule> validated) implements Of {

        public WellFounded {
            validated = Set.copyOf(validated);
        }
    }

    /**
     * One declaration reaches itself, and the spreads it goes round by.
     *
     * @param declaration the declaration the ring closes on, which is where an author is sent
     * @param round the spreads as they are written, beginning with the one written on
     *     {@code declaration} and ending with the one that reaches it again
     */
    public record ReachesItself(TypeSymbol.AtModule declaration, List<Hir.Name> round)
            implements Of {

        public ReachesItself {
            round = List.copyOf(round);
        }

        /** Where the report goes: the first spread of the ring, which is written on
         *  {@link #declaration} and is one an author can take out. */
        public Hir.Name written() {
            return round.get(0);
        }

        /**
         * Whether {@code module} is the one that wrote this ring, and so the one to report it.
         *
         * <p>A walk goes wherever the spreads go, so a module that spreads its way into somebody
         * else's ring finds it and is not where it is written. Asked of the ring rather than
         * worked out beside each report, because every reader that finds one has to decide the
         * same thing and there is one answer to decide it by.
         *
         * <p>Whichever declaration of a ring the walk closed on will do: a spread out of a module
         * and back is two modules importing each other, so the whole of a ring is written in one
         * module.
         */
        public boolean writtenIn(String module) {
            return declaration.module().equals(module);
        }

        /** The ring as a reader is shown it — the spreads in the order they are gone round by. */
        public String through() {
            List<String> names = new ArrayList<>();
            for (Hir.Name each : round) {
                names.add("`" + each.written() + "`");
            }
            return String.join(" -> ", names);
        }
    }

    /**
     * Whether anything {@code declared} reaches through its spreads reaches a declaration it is
     * written under.
     *
     * <p>The first ring found, and not all of them. A declaration that reaches itself is one the
     * author has to take apart, and what the rest of the graph does under it is not something they
     * can act on until they have.
     */
    public static Of of(List<TypeSymbol.AtModule> declared, Declarations declarations) {
        Walk walk = new Walk(declarations);
        for (TypeSymbol.AtModule each : declared) {
            ReachesItself found = walk.from(each);
            if (found != null) {
                return found;
            }
        }
        return new WellFounded(walk.finished);
    }

    /**
     * The three states of a depth-first walk, held as two collections.
     *
     * <p>{@code path} is what the walk is currently inside and {@code finished} what it has come back
     * out of; a declaration in neither has not been reached. A spread into {@code path} closes a
     * ring, and one into {@code finished} is a declaration reached twice — which the walk is done
     * with and need not enter again, because whether that declaration reaches itself has an answer
     * already and does not turn on who arrived at it.
     */
    private static final class Walk {

        private final Declarations declarations;
        private final Set<TypeSymbol.AtModule> finished = new LinkedHashSet<>();
        private final List<TypeSymbol.AtModule> path = new ArrayList<>();
        /** The spread taken out of each declaration on the path, so {@code taken.get(i)} is written
         *  on {@code path.get(i)} and reaches {@code path.get(i + 1)}. */
        private final List<Hir.Name> taken = new ArrayList<>();

        private Walk(Declarations declarations) {
            this.declarations = declarations;
        }

        private ReachesItself from(TypeSymbol.AtModule named) {
            if (finished.contains(named)) {
                return null;
            }
            // Only a product spreads. A sum reaching itself through its cases is a different rule
            // and is refused where the sum is checked; a name nothing declares was reported where
            // it is written.
            if (!(declarations.at(named) instanceof Hir.Data data)) {
                finished.add(named);
                return null;
            }
            path.add(named);
            for (Hir.Name written : data.includes()) {
                Hir.Name.Denoting denoting = written.answered();
                if (denoting == null
                        || !(denoting.type() instanceof TypeSymbol.AtModule reached)) {
                    continue;
                }
                int closes = path.indexOf(reached);
                if (closes >= 0) {
                    List<Hir.Name> round = new ArrayList<>(taken.subList(closes, taken.size()));
                    round.add(written);
                    return new ReachesItself(reached, round);
                }
                taken.add(written);
                ReachesItself found = from(reached);
                if (found != null) {
                    return found;
                }
                taken.remove(taken.size() - 1);
            }
            path.remove(path.size() - 1);
            finished.add(named);
            return null;
        }
    }
}
