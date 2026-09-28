package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.jvm.ClassFileImage;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A primitive standing as a case of a union is held on the JVM as its box, and every reader that
 * tells the cases apart tests it as that box: a {@code match}, the routing between a composition's
 * stages, and what a behavior answers.
 *
 * <p>So where the value is held unboxed and the type it stands as is not, standing as that type is a
 * change of representation, made wherever it stands — a binding, a branch, a helper's parameter —
 * and not only where a behavior returns it. A reference already is what it stands as, so a
 * {@code String} case and a declared case are not boxed.
 *
 * <p>Every class a module generates is loaded before anything runs, so a body that does not verify
 * fails here even where no test reaches it.
 */
class APrimitiveStandingAsAUnionIsHeldAsItsBoxTest {

    private static final String HEAD = """
            module demo

            data In = { n: Int }
            data Out = { n: Int }
            data A = { a: Int }
            data Missing

            """;

    @Test
    void anIntBoundAsAUnionIsMatchedAsItsCase() throws Exception {
        assertEquals(5L, out(run(HEAD + """
                behavior run : (i: In) -> Out constructs Out
                let run (i) = {
                    let r: Int | Missing = i.n
                    match r with
                        | Int as q -> Out { n = q }
                        | Missing -> Out { n = 0 }
                }
                """, 5L)));
    }

    @Test
    void aBoolBoundAsAUnionIsMatchedAsItsCase() throws Exception {
        assertEquals(1L, out(run(HEAD + """
                behavior run : (i: In) -> Out constructs Out
                let run (i) = {
                    let r: Bool | Missing = i.n > 1
                    match r with
                        | Bool as q -> Out { n = if q then 1 else 2 }
                        | Missing -> Out { n = 0 }
                }
                """, 5L)));
    }

    @Test
    void aStringBoundAsAUnionIsMatchedAsItsCase() throws Exception {
        assertEquals(3L, out(run(HEAD + """
                behavior run : (i: In) -> Out constructs Out
                let run (i) = {
                    let r: String | Missing = "abc"
                    match r with
                        | String as q -> Out { n = String.length(q) }
                        | Missing -> Out { n = 0 }
                }
                """, 5L)));
    }

    @Test
    void aDeclaredCaseBoundAsAUnionIsMatchedAsItsCase() throws Exception {
        assertEquals(5L, out(run(HEAD + """
                behavior run : (i: In) -> Out constructs Out, A
                let run (i) = {
                    let r: A | Missing = A { a = i.n }
                    match r with
                        | A as u -> Out { n = u.a }
                        | Missing -> Out { n = 0 }
                }
                """, 5L)));
    }

    @Test
    void anIntMeetingAnotherCaseAtABranchIsMatchedAsItsCase() throws Exception {
        String model = HEAD + """
                behavior run : (i: In) -> Out constructs Out
                let run (i) = {
                    let r: Int | Missing = if i.n > 1 then i.n else Missing
                    match r with
                        | Int as q -> Out { n = q }
                        | Missing -> Out { n = 0 }
                }
                """;
        assertEquals(5L, out(run(model, 5L)));
        assertEquals(0L, out(run(model, 1L)));
    }

    @Test
    void anIntHandedToAParameterTypedAsAUnionIsMatchedAsItsCase() throws Exception {
        assertEquals(5L, out(run(HEAD + """
                behavior run : (i: In) -> Out constructs Out
                let pick (v: Int | Missing): Int = match v with
                    | Int as q -> q
                    | Missing -> 0
                let run (i) = Out { n = pick(i.n) }
                """, 5L)));
    }

    /** Where the value comes to stand as the union does not change what the behavior answers: bound
     * first, it is boxed where it is bound; answered directly, where it is returned. */
    @Test
    void anAnswerIsTheSameWhereverItCameToStandAsTheUnion() throws Exception {
        Object bound = run(HEAD + """
                behavior run : (i: In) -> Int | Missing
                let run (i) = {
                    let r: Int | Missing = i.n
                    r
                }
                """, 5L);
        Object direct = run(HEAD + """
                behavior run : (i: In) -> Int | Missing
                let run (i) = i.n
                """, 5L);
        // Two modules, two loaders: the classes differ, so the answers are compared as they read.
        assertEquals("IntCase[value=5]", String.valueOf(direct));
        assertEquals(String.valueOf(direct), String.valueOf(bound));
    }

    @Test
    void aCompositionRoutesAnIntCaseToTheStageTakingIt() throws Exception {
        Object behavior = behavior(HEAD + """
                behavior parse : (n: Int) -> Int | Missing
                let parse (n) = {
                    let found: Int | Missing = n
                    let missing: Int | Missing = Missing
                    if n > 0 then found else missing
                }
                behavior double : (n: Int) -> Int
                let double (n) = n * 2
                behavior run = parse >-> double
                """);
        assertEquals("IntCase[value=10]", String.valueOf(Codecs.apply(behavior, 5L)));
        assertEquals("Missing[]", String.valueOf(Codecs.apply(behavior, -1L)));
    }

    @Test
    void aCompositionRoutesAStringCaseToTheStageTakingIt() throws Exception {
        Object behavior = behavior(HEAD + """
                behavior parse : (n: Int) -> String | Missing
                let parse (n) = {
                    let found: String | Missing = "x"
                    let missing: String | Missing = Missing
                    if n > 0 then found else missing
                }
                behavior shout : (s: String) -> String
                let shout (s) = s ++ "!"
                behavior run = parse >-> shout
                """);
        assertEquals("StringCase[value=x!]", String.valueOf(Codecs.apply(behavior, 5L)));
        assertEquals("Missing[]", String.valueOf(Codecs.apply(behavior, -1L)));
    }

    /** What an injected behavior answers is bound where the call is made, by a path of its own. Its
     * implementation is Java, so this loads the body rather than running it. */
    @Test
    void anIntAnInjectedBehaviorAnswersIsBoundAsAUnion() {
        loaded(HEAD + """
                behavior inner : (i: In) -> Int
                behavior run : (i: In) -> Out constructs Out depends on inner
                let run (i, inner) = {
                    let r: Int | Missing = inner(i)
                    match r with
                        | Int as q -> Out { n = q }
                        | Missing -> Out { n = 0 }
                }
                """);
    }

    private Object run(String model, long n) throws Exception {
        BytesClassLoader loader = loaded(model);
        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        return Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", Map.of("n", n)));
    }

    private Object behavior(String model) throws Exception {
        return Emitted.behavior(loaded(model), "demo", "run").getConstructor().newInstance();
    }

    private Object out(Object value) throws Exception {
        return ((Map<?, ?>) Codecs.encode(value.getClass().getClassLoader(), "demo.Out", value)).get("n");
    }

    /** The model's classes, every one of them loaded and so verified. */
    private BytesClassLoader loaded(String model) {
        Map<String, ClassFileImage> classes = Compiler.compile(model);
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        for (String name : classes.keySet()) {
            try {
                Class.forName(name.replace('/', '.'), true, loader);
            } catch (ClassNotFoundException e) {
                throw new AssertionError("a generated class did not load: " + name, e);
            }
        }
        return loader;
    }
}
