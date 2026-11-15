package souther.compiler.query;

import souther.compiler.ACompiledModel;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a combination the classes do not state is owed a row is answered by a row: one a search
 * composed and a run was seen making it with. Until then the combination is counted and a finding
 * says it is open, and nothing is refused over it. One whose decisions state relations no value
 * holds together is no combination at all.
 */
class ACombinationTheClassesCannotSayExistsIsOwedOnceARunIsSeenMakingItTest {

    private static List<Adequacy.Finding> findingsOf(String model, String module) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return compilation.db().ask(new Adequacy.Findings(module)).value().stream()
                .filter(each -> each.about() instanceof About.ACombinationNoRowMakes).toList();
    }

    /** A relation two rows can each be written for, so a run is seen making each. */
    @Test
    void aCombinationARunIsSeenMakingIsAGapAndOneNoValueHoldsIsNoCombination() {
        List<Adequacy.Finding> findings = findingsOf("""
                module example.fee

                behavior fee : (x: Int, y: Int) -> Int

                let fee (x, y) =
                    (if x == y then 10 else 20) + (if x > y then 1 else 2)

                example fee
                    | (1, 2) -> 22
                """, "example.fee");

        // x == y with x > y is no combination: the relations the two decisions state leave no
        // value, so it is not asked for. Of the three left, the row made one.
        assertEquals(2, findings.size(), () -> "the combinations the row did not make: " + findings);
        assertTrue(findings.stream().allMatch(Adequacy.Finding::established),
                () -> "and a run is seen making each of them, so each is owed a row: " + findings);
    }
}
