package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A behavior's output union carries a derived encoder that dispatches its cases by the discriminator
 * {@code "type"}, the way a named sum over the same leaves does (spec 19.8, 11.2). Without it the
 * same value would travel two ways depending on where it sat — a sum answered bare would lose the
 * discriminator its own field-borne form writes.
 */
class CompileOutputUnionEncoderTest {

    @Test
    void aProductMemberLaysItsFieldsFlatUnderTheTypeTag() throws Exception {
        BytesClassLoader loader = compileBill();
        Object ok = Codecs.apply(loader.loadClass("m.Bill").getMethod("of").invoke(null), 5L);
        assertEquals(Map.of("v", 5L, "type", "Ok"), Codecs.encode(loader, "m.BillResult", ok));
    }

    @Test
    void aUnitMemberWritesTheTypeTagAlone() throws Exception {
        BytesClassLoader loader = compileBill();
        Object none = Codecs.apply(loader.loadClass("m.Bill").getMethod("of").invoke(null), 0L);
        assertEquals(Map.of("type", "NotFound"), Codecs.encode(loader, "m.BillResult", none));
    }

    @Test
    void aPrimitiveMemberPutsItsValueUnderValue() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module m exposing ( NoAnswer, half )
                data NoAnswer
                behavior half : (n: Int) -> Int | NoAnswer
                    constructs NoAnswer
                let half (n) = if n >= 0 then n / 2 else NoAnswer
                """), getClass().getClassLoader());
        Object answered = Codecs.apply(loader.loadClass("m.Half").getMethod("of").invoke(null), 7L);
        assertEquals(Map.of("type", "Int", "value", 3L),
                Codecs.encode(loader, "m.HalfResult", answered));
    }

    @Test
    void anImportedNewtypeMemberPutsItsValueUnderValue() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compileModules(List.of("""
                module up exposing ( Yen )
                data Yen = Int
                    invariant value >= 0
                """, """
                module down exposing ( NothingOwed, owed )
                import up ( Yen )
                data NothingOwed
                behavior owed : (a: Yen) -> Yen | NothingOwed
                    constructs Yen, NothingOwed
                let owed (a) = if a.value > 0 then Yen(a.value) else NothingOwed
                """)), getClass().getClassLoader());
        Object owed = loader.loadClass("down.Owed").getMethod("of").invoke(null);
        Object answered = Codecs.apply(owed, Codecs.decoded(loader, "up.Yen", 5L));
        assertEquals(Map.of("type", "Yen", "value", 5L),
                Codecs.encode(loader, "down.OwedResult", answered));
    }

    @Test
    void aUnionOfUnitsTravelsAsItsCaseName() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module m exposing ( Approved, Rejected, decide )
                data Approved
                data Rejected
                behavior decide : (n: Int) -> Approved | Rejected
                    constructs Approved, Rejected
                let decide (n) = if n > 0 then Approved else Rejected
                """), getClass().getClassLoader());
        Object decide = loader.loadClass("m.Decide").getMethod("of").invoke(null);
        assertEquals("Approved", Codecs.encode(loader, "m.DecideResult", Codecs.apply(decide, 1L)));
        assertEquals("Rejected", Codecs.encode(loader, "m.DecideResult", Codecs.apply(decide, 0L)));
    }

    @Test
    void aNamedSumMemberIsTaggedByTheLeafItAnsweredWith() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module m exposing ( Hit, Miss, Answer, NoAnswer, ask )
                data Hit = { score: Int }
                data Miss = { reason: String }
                data Answer = Hit | Miss
                data NoAnswer
                behavior ask : (n: Int) -> Answer | NoAnswer
                    constructs Hit, Miss, NoAnswer
                let ask (n) = {
                    guard n >= 0 else NoAnswer
                    if n > 0 then Hit { score = n } else Miss { reason = "no" }
                }
                """), getClass().getClassLoader());
        Object ask = loader.loadClass("m.Ask").getMethod("of").invoke(null);
        assertEquals(Map.of("type", "Hit", "score", 3L),
                Codecs.encode(loader, "m.AskResult", Codecs.apply(ask, 3L)));
    }

    @Test
    void whatTheUnionWritesForASumsLeafIsWhatThatSumReadsBack() throws Exception {
        // The round-trip the discriminator is for: a sum answered bare and the same sum answered
        // inside a field write one form, so either can be read by the sum's own decoder.
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module m exposing ( Hit, Miss, Answer, NoAnswer, ask )
                data Hit = { score: Int }
                data Miss = { reason: String }
                data Answer = Hit | Miss
                data NoAnswer
                behavior ask : (n: Int) -> Answer | NoAnswer
                    constructs Hit, Miss, NoAnswer
                let ask (n) = {
                    guard n >= 0 else NoAnswer
                    if n > 0 then Hit { score = n } else Miss { reason = "no" }
                }
                """), getClass().getClassLoader());
        Object hit = Codecs.apply(loader.loadClass("m.Ask").getMethod("of").invoke(null), 3L);
        Object written = Codecs.encode(loader, "m.AskResult", hit);
        assertEquals(hit, Codecs.decoded(loader, "m.Answer", written));
    }

    private BytesClassLoader compileBill() {
        return new BytesClassLoader(Compiler.compile("""
                module m exposing ( Ok, NotFound, bill )
                data Ok = { v: Int }
                data NotFound
                behavior bill : (n: Int) -> Ok | NotFound
                    constructs Ok, NotFound
                let bill (n) = if n > 0 then Ok { v = n } else NotFound
                """), getClass().getClassLoader());
    }
}
