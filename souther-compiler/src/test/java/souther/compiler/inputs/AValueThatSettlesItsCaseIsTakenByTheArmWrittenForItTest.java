package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * The case a value settles is said in the atoms the checker resolves an arm's cases to cover, so
 * the arm written for it takes it and no other does — for every kind of case.
 *
 * <p>Asked of the arms as the checker built them and of values made here, since an optional's
 * carrier is written only into a field and no model hands one to a {@code match} as written. What
 * is held is the agreement between the two vocabularies, which is what the answer is for wherever a
 * carrier reaches one.
 */
class AValueThatSettlesItsCaseIsTakenByTheArmWrittenForItTest {

    private static final SourcePos HERE = new SourcePos(0, 0);

    private static final String MODEL = """
            module m

            data Held = { held: Int? }
            data Missing
            data Station = { at: String }
            data Hospital = { at: String }
            data Renkei = { at: String }
            data OnceKind = Station | Hospital
            data VisitKind = OnceKind | Renkei

            behavior opt : (h: Held) -> Int
            let opt (h) =
                match h.held with
                    | Some x -> x
                    | None -> 0

            let choose (v: Int | Missing): Int =
                match v with
                    | Int as q -> q
                    | Missing -> 0

            behavior pick : (n: Int) -> Int
            let pick (n) = choose(n)

            behavior fee : (k: VisitKind) -> Int
            let fee (k) =
                match k with
                    | OnceKind -> 1
                    | Renkei -> 2
            """;

    @Test
    void anOptionalsCarriersAreTakenByTheirOwnArms() {
        Core.Match match = matchOf("opt");
        Type option = match.scrutinee().type();
        assertEquals(List.of(true, false),
                taken(match, new Core.OptionSome(new Core.Int(4, Type.Prim.INT, HERE), option, HERE)));
        assertEquals(List.of(false, true), taken(match, new Core.OptionNone(option, HERE)));
    }

    @Test
    void aPrimitiveIsTakenByTheArmForIt() {
        assertEquals(List.of(true, false),
                taken(matchOf("pick"), new Core.Int(3, Type.Prim.INT, HERE)));
    }

    @Test
    void aConstructionIsTakenByTheArmForTheSumOverIt() {
        Core.Match match = matchOf("fee");
        TypeSymbol.AtModule station = (TypeSymbol.AtModule) match.cases().get(0).pattern()
                .cases().get(0).atoms().get(0);
        assertEquals("Station", station.name(), "the first leaf under OnceKind");
        Core made = new Core.Construct(station, List.of(), Type.ref(station), HERE);
        assertEquals(List.of(true, false), taken(match, made));
    }

    /** Whether every row takes each arm, the value standing as what the {@code match} is over. */
    private static List<Boolean> taken(Core.Match match, Core value) {
        Optional<TypeSymbol> written =
                WrittenCase.of(Core.standingAs(value, match.scrutinee().type()));
        assertEquals(true, written.isPresent(), () -> value + " settles its case");
        return match.cases().stream()
                .map(arm -> InputReads.whetherEveryRowTakes(arm, Set.of(written.get())).orElseThrow())
                .toList();
    }

    private static Core.Match matchOf(String behavior) {
        Compilation compilation = Compilation.ofSources(List.of(MODEL), ModulePath.EMPTY);
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().literalMessage())
                .toList(), "the model compiles");
        Core body = compilation.db().ask(new Bodies.Checked(compilation.modules().get(0))).value()
                .behaviorBodies().get(behavior);
        assertNotNull(body, () -> "the model compiles: " + compilation.errors());
        Core.Match match = firstMatch(body);
        assertNotNull(match, "the body matches");
        return match;
    }

    private static Core.Match firstMatch(Core at) {
        if (at instanceof Core.Match match) {
            return match;
        }
        Core.Match[] found = new Core.Match[1];
        Core.forEachChild(at, each -> {
            if (found[0] == null) {
                found[0] = firstMatch(each);
            }
        });
        return found[0];
    }
}
