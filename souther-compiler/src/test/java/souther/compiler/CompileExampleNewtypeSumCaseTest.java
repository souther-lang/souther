package souther.compiler;

import org.junit.jupiter.api.Test;

/**
 * A fixture may name a newtype case of a sum. Such a case decodes from the adjacent form — its inner
 * value under {@code value}, next to the discriminator — while a fixture names it the way the domain
 * constructs it, {@code Verified(Addr("a@example.com"))}. The builder handed over the bare inner
 * value, so the sum's decoder was given a string where it wanted an object, in both the positions a
 * sum can occupy.
 */
class CompileExampleNewtypeSumCaseTest {

    private static final String BASE = """
            module demo

            data Addr = String
            data Verified = Addr
            data Unverified = Addr
            data Mail = Verified | Unverified

            data Out = { ok: Bool }
            """;

    @Test
    void aNewtypeSumCaseNestedInARecordField() {
        Compiler.compile(BASE + """
                data Person = { id: String, mail: Mail }

                behavior check : (p: Person) -> Out constructs Out
                let check (p) = Out { ok = match p.mail with | Verified -> true | Unverified -> false }

                example check
                  | "verified" : (Person { id = "p-1", mail = Verified(Addr("a@example.com")) })
                        -> Out { ok = true }
                  | "unverified" : (Person { id = "p-2", mail = Unverified(Addr("b@example.com")) })
                        -> Out { ok = false }
                """);
    }

    @Test
    void aNewtypeSumCaseAsTheArgumentItself() {
        Compiler.compile(BASE + """
                behavior direct : (m: Mail) -> Out constructs Out
                let direct (m) = Out { ok = match m with | Verified -> true | Unverified -> false }

                example direct
                  | "verified" : (Verified(Addr("a@example.com"))) -> Out { ok = true }
                  | "unverified" : (Unverified(Addr("b@example.com"))) -> Out { ok = false }
                """);
    }

    @Test
    void aNewtypeThatIsNobodysCaseIsStillItsBareValue() {
        // the wrap applies only to a case of a sum; a plain newtype's neutral form is unchanged
        Compiler.compile("""
                module demo

                data Addr = String
                data Out = { ok: Bool }

                behavior check : (a: Addr) -> Out constructs Out
                let check (a) = Out { ok = String.contains("@", a.value) }

                example check
                  | "an address" : (Addr("a@example.com")) -> Out { ok = true }
                """);
    }
}
