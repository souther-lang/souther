package souther.compiler;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A name an arm gives the matched value stands for the scrutinee. When the scrutinee is a helper's
 * {@code match}, the invariant check reads the caller once per arm of that helper, and in the arm
 * answering a unit the scrutinee is only that unit. The caller's arm for {@code Int} is then one no
 * run enters, and its name must not be read as the unit: a construction over it
 * would state a newtype's invariant of a unit.
 */
class AnArmNamingACaseTheScrutineeCannotBeIsNotReadAsThatValueTest {

    private static final String DECLARATIONS = """
            module v

            data 形が違う
            data 番号 = Int
                invariant 一以上 = value >= 1
            data 失敗

            """;

    private static final String HELPER_UNIT_FIRST = """
            let 整数 (s: String): Int | 形が違う =
                match String.toInt(s) with
                    | NotANumber -> 形が違う
                    | Int as n -> n

            """;

    private static final String HELPER_INT_FIRST = """
            let 整数 (s: String): Int | 形が違う =
                match String.toInt(s) with
                    | Int as n -> n
                    | NotANumber -> 形が違う

            """;

    private static final String BUILDS_A_NEWTYPE = """
            behavior 読む : (s: String) -> 番号 | 失敗
                constructs 番号

            let 読む (s) =
                match 整数(s) with
                    | 形が違う -> 失敗
                    | Int as n -> {
                        guard 番号(n) as x else
                            | 一以上 -> 失敗
                        x
                    }
            """;

    private static final String BUILDS_A_NEWTYPE_INT_ARM_FIRST = """
            behavior 読む : (s: String) -> 番号 | 失敗
                constructs 番号

            let 読む (s) =
                match 整数(s) with
                    | Int as n -> {
                        guard 番号(n) as x else
                            | 一以上 -> 失敗
                        x
                    }
                    | 形が違う -> 失敗
            """;

    private static void compiles(String helper, String caller) {
        assertFalse(Compiler.compile(DECLARATIONS + helper + caller).isEmpty());
    }

    @Test
    void aNewtypeBuiltFromTheNumberCompilesWhicheverArmIsWrittenFirst() {
        compiles(HELPER_UNIT_FIRST, BUILDS_A_NEWTYPE);
        compiles(HELPER_UNIT_FIRST, BUILDS_A_NEWTYPE_INT_ARM_FIRST);
        compiles(HELPER_INT_FIRST, BUILDS_A_NEWTYPE);
        compiles(HELPER_INT_FIRST, BUILDS_A_NEWTYPE_INT_ARM_FIRST);
    }

    /** A helper whose scrutinee is another helper's {@code match} is read once per arm of each. */
    @Test
    void aNewtypeBuiltThroughTwoHelpersCompiles() {
        compiles("""
                let 整数 (s: String): Int | 失敗 =
                    match String.toInt(s) with
                        | NotANumber -> 失敗
                        | Int as n -> n

                let 外 (s: String): Int | 失敗 =
                    match 整数(s) with
                        | 失敗 -> 失敗
                        | Int as n -> n

                """, """
                behavior 読む : (s: String) -> 番号 | 失敗
                    constructs 番号

                let 読む (s) =
                    match 外(s) with
                        | 失敗 -> 失敗
                        | Int as n -> {
                            guard 番号(n) as x else
                                | 一以上 -> 失敗
                            x
                        }
                """);
    }
}
