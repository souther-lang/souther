package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A guard on how many elements a flatMap makes over another flatMap's answer turns on the
 * comparison inside it, and is carried to that comparison whatever the inner flatMap writes: one
 * element of each piece, or the piece's value where it is made into a newtype and none where it is
 * not. The guard is not dropped from the report: the comparison is read for the places it relates,
 * and the guard's own rules are there to be taken.
 */
class AGuardOverAFlatMapOfAnAttemptedConstructionIsCarriedToTheComparisonItTurnsOnTest {

    private static String reported(String inner) {
        Compilation compilation = ACompiledModel.measured("""
                module h11

                data D = String
                    invariant String.matches("[a-z.]+", value)

                behavior f : (email: String, doms: List<String>) -> Int
                CONSTRUCTS

                let f (email, doms) = {
                    let ma = List.flatMap(d -> List.filter(a -> a == d, doms),
                                          List.flatMap(INNER, List.drop(1, String.split("@", email))))
                    guard List.length(ma) >= 1 else 0
                    1
                }
                """.replace("INNER", inner)
                .replace("CONSTRUCTS", inner.contains("D(") ? "    constructs D" : ""),
                Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()))
                .replaceAll("@\\d+:\\d+", "").replaceAll("at \\d+:\\d+", "at");
    }

    private static void theGuardIsCarriedToTheEquality(String inner, String report) {
        assertTrue(report.contains("doms[*] is divided by comparison"), () -> inner + report);
        assertTrue(report.contains("the comparison at holds")
                && report.contains("the comparison at does not hold"), () -> inner + report);
        assertFalse(report.contains("about a value made from this one"), () -> inner + report);
    }

    @Test
    void theGuardIsCarriedToTheEqualityWhereTheInnerFlatMapWritesThePiece() {
        String inner = "p -> [ p ]";

        theGuardIsCarriedToTheEquality(inner, reported(inner));
    }

    /** Where the piece is made into a newtype by an attempt, the guard is carried as well, and no
     *  run stops at the attempt: one it refuses takes the other arm. */
    @Test
    void theGuardIsCarriedToTheEqualityWhereThePieceIsMadeIntoANewtype() {
        String inner = "p -> if D(p) as n then [ n.value ] else []";
        String report = reported(inner);

        theGuardIsCarriedToTheEquality(inner, report);
        assertFalse(report.contains(UnreadBesideItsStops.STOPS_NOT_ALL_TOLD), report);
    }

    /**
     * A known limit, held so that lifting it is seen. The newtype holds only some strings, so the
     * equality divides the string the pieces are of as well. That is not read yet: the relation
     * reads the attempt's value through to the piece and keeps nothing of what the attempt asked
     * of it, so it reads the equality as it does where the piece is not made into one. Once it
     * keeps that, this fails: assert the division here instead.
     */
    @Test
    void theStringThePiecesAreOfIsNotYetDividedByWhatTheAttemptAsksOfAPiece() {
        String report = reported("p -> if D(p) as n then [ n.value ] else []");

        assertFalse(report.contains("email is divided by comparison"), report);
    }
}
