package souther.bench;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A way past the figure read again for a relation is read for that relation and for nothing else,
 * over every module the reactor builds.
 *
 * <p>What the reading again comes to drops conditions the relation does not read and puts each
 * choice it does read at the parts that bear on it. That is the way as one relation sees it, and
 * it is not the way: the generator composes along the conditions as they were written, the
 * coverage owes a line to each writing of a condition, and the reports name each where it stands.
 * A reader that took the way read again for any of those — a cache of it shared between relations,
 * a projection handed to the generator to spare it the walk — would lose a writing of a condition,
 * an obligation, or a place a report is sent to, and nothing it reads would say so.
 *
 * <p>So the places that ask for it are the relation's own reading of the ways a row arrives
 * along: the reading again, and the splitting of the ways into branches that reads what it came
 * to. Both directions are asserted: the places are expected, so a check that read nothing fails.
 */
class AWayReadForARelationIsReadForThatRelationAloneTest {

    private static final String READ_AGAIN = "souther.compiler.partition.AWayReadForARelation";

    @Test
    void onlyTheRelationsReadingAsksForAWayReadAgain() {
        Set<String> asking = new LinkedHashSet<>();
        for (Compiled.Site site : Compiled.sites()) {
            if (inTheNest(site.owner()) && !inTheNest(site.from())) {
                asking.add(site.at());
            }
        }
        assertEquals(List.of("souther.compiler.partition.UndividedByARelation#branchesOf("
                        + "Lsouther/compiler/partition/Reachability$Reaching;Ljava/util/List;"
                        + "Lsouther/compiler/inputs/InputReading;Ljava/util/Set;)Z",
                        "souther.compiler.partition.UndividedByARelation#readAgainForThis("
                        + "Lsouther/compiler/partition/Reachability$Ways$Whole;"
                        + "Lsouther/compiler/inputs/InputReading;)"
                        + "Lsouther/compiler/partition/AWayReadForARelation$ReadAgain;"),
                List.copyOf(asking),
                "a way read again for a relation is asked for by something that is not the"
                        + " relation's reading of the ways a row arrives along");
    }

    private static boolean inTheNest(String type) {
        return type.equals(READ_AGAIN) || type.startsWith(READ_AGAIN + "$");
    }
}
