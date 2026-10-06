package souther.compiler.partition;

import souther.compiler.Compiler;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.reading.CoverageRead;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A value settled by an arm for several cases is a factor whose outcome places a row.
 *
 * <p>The arm admits each case it names, so a combination taking it is one a row in any of them
 * sits in. Read as a case no class has, the outcome placed at nothing and the whole group went.
 */
class AnArmForSeveralCasesPlacesACellTest {

    @Test
    void aGroupWithAFactorSettledByAnArmForSeveralCasesIsOffered() {
        Compilation compilation = Compiler.analyzedModules(List.of("""
                module example.several

                data A
                data B
                data C
                data Kind = A | B | C

                data On
                data Off
                data Flag = On | Off

                data Fee = Int
                    invariant value >= 0

                behavior total : (k: Kind, f: Flag) -> Fee
                    constructs Fee

                let total (k, f) = Fee((match k with
                                            | A | B -> 1
                                            | C -> 2)
                                        + (match f with
                                            | On -> 10
                                            | Off -> 0))
                """), ModulePath.EMPTY, new ArrayList<>(), Adequacy.Asked.fullReport());
        CoverageRead.Read read = compilation.db()
                .ask(new Adequacy.Meets("example.several")).value().get("total");
        List<Axis> axes = compilation.db()
                .ask(new Adequacy.Divided("example.several", "total")).value().axes();

        InteractionCells.Offered offered = InteractionCells.of(read.interactions(), axes,
                Budgets.generation().cellsPerGroup());

        assertEquals(1, offered.groups().size(),
                () -> "the two values meeting at the sum are one group: " + read.interactions());
        assertEquals(4, offered.groups().getFirst().left(0),
                () -> "two outcomes of each, every one of them placing a row");
    }
}
