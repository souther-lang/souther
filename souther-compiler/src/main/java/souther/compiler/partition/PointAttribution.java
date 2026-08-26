package souther.compiler.partition;

import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;

/**
 * Whose account one point a row is owed at falls in.
 *
 * <p>The one answer read off what settled the point ({@link PointContributions}), and the only
 * thing downstream is given: a row here is this reading's to write, or it is owed to the
 * declarations that put the line there and one row anywhere in the module settles it. A reader
 * handed the contributors instead has to ask the question itself, and a reader that forgets to ask
 * measures a body against a line no row written for it is owed.
 *
 * <p><b>Read once, when everything that settled the point has arrived.</b> A point's own line and
 * whatever stops the region beside it are gathered as the reading works the region out, and either
 * of them alone answers about itself rather than about the point. So the contributors are what can
 * be added to and this is what is concluded, and nothing here can be added to.
 *
 * <p><b>Two arms and no third, because a row here is somebody's to write.</b> Written as "not the
 * declarations'", a value nothing contributed to would answer that a body owes the row, and a value
 * everything contributed to would have to be read twice to find out which.
 */
public sealed interface PointAttribution {

    /**
     * A body's, because a rule written in one settled it.
     *
     * <p>A comparison states something about that body at that position, so a run that stops at one
     * exists in that body and nowhere else, and a row for it is written for this behavior.
     */
    record TheReading() implements PointAttribution {

        public static final TheReading INSTANCE = new TheReading();
    }

    /**
     * The declarations', because nothing but clauses and the declarations that took the position in
     * settled it.
     *
     * <p>What such a row shows is a fact about the type — whether a string of one character is a
     * {@code Sku} is the same question wherever a {@code Sku} goes — so one row anywhere in the
     * module settles it, and the behaviors carrying the type have nothing to add.
     *
     * @param owners every declaration that owes a row here, in the order they contributed. Never
     *               empty: an arm saying the declarations owe it and naming none of them would be a
     *               debt with nobody to answer for it
     */
    record TheDeclarations(List<TypeSymbol.AtModule> owners) implements PointAttribution {

        public TheDeclarations {
            owners = List.copyOf(owners);
            if (owners.isEmpty()) {
                throw new IllegalArgumentException(
                        "a point owed to the declarations is owed to some declaration");
            }
        }

        /**
         * Which of them {@code module} wrote, in the order this names them.
         *
         * <p>What a module's account of this point is filed under. A point with none of these here
         * is one this module has nothing to answer for: its values are held to the line, and a row
         * at it is somebody else's to write.
         */
        public List<TypeSymbol.AtModule> ownersIn(String module) {
            return owners.stream().filter(each -> module.equals(each.module())).toList();
        }

        /**
         * This and {@code also}, each owner once.
         *
         * <p>Two readings of one point, each naming what settled it where it was read. A point one
         * module's declaration narrowed at one position and another's at another is owed to both.
         * A union of owners and not a second classification: both sides are already the
         * declarations'.
         */
        public TheDeclarations and(TheDeclarations also) {
            List<TypeSymbol.AtModule> both = new ArrayList<>(owners);
            also.owners.stream().filter(each -> !both.contains(each)).forEach(both::add);
            return new TheDeclarations(both);
        }
    }

    /**
     * What the contributors come to.
     *
     * <p>The one place this is decided. Everything that measures a behavior, counts what it covers,
     * raises a finding about it or offers it a row reads the answer rather than the contributors, so
     * there is nowhere for the rule to be remembered wrongly.
     *
     * @throws IllegalArgumentException where nothing contributed, which is not a point either side
     *                                  owes a row at. A claim about the end of the order carries
     *                                  such a value, and the point it is part of is settled by the
     *                                  line the region lies beside as well
     */
    static PointAttribution of(PointContributions contributions) {
        if (contributions.isEmpty()) {
            throw new IllegalArgumentException(
                    "a point nothing settled, which nobody can be owed a row at");
        }
        return contributions.allDeclarations()
                ? new TheDeclarations(contributions.owners()) : TheReading.INSTANCE;
    }
}
