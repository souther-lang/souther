package souther.compiler.meta;

import souther.compiler.Emitted;
import souther.compiler.Compiler;

import org.junit.jupiter.api.Test;

import java.lang.classfile.Annotation;
import java.lang.classfile.AnnotationElement;
import java.lang.classfile.AnnotationValue;
import java.lang.classfile.ClassFile;
import java.lang.classfile.attribute.RuntimeInvisibleAnnotationsAttribute;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A compiled module carries what it declares, so another project can import it from a jar with no
 * {@code .sou} of its own. Each definition rides on the class it generated, as the source that
 * declared it; the module's own facts ride on a {@code $Module} class emitted for them.
 */
class ModuleMetadataTest {

    private static final String UP = """
            module shared.money exposing ( Amount, charge )
            import String ( length )

            // what a payment is worth
            data Amount = Int
                invariant value >= 0 && withinCap(value)

            data Receipt = { paid: Amount }
            data Declined

            behavior charge : (a: Amount) -> Receipt | Declined
                constructs Receipt
            let charge (a) = if a.value > 0 then Receipt { paid = a } else Declined

            let withinCap (n: Int) = n <= 1000000
            let unrelated (n: Int) = n + 1
            """;

    @Test
    void aDataCarriesTheDeclarationThatDeclaredIt() {
        Map<String, byte[]> classes = Compiler.compile(UP);

        assertEquals("""
                // what a payment is worth
                data Amount = Int
                    invariant value >= 0 && withinCap(value)""",
                string(annotation(classes, "shared.money.Amount", "SoutherData"), "value"));
    }

    @Test
    void aBehaviorCarriesItsSignatureAndWhereItsBodyComesFrom() {
        Map<String, byte[]> classes = Compiler.compile(UP);

        Annotation charge = annotation(classes, "shared.money.Charge", "SoutherBehavior");
        assertEquals("""
                behavior charge : (a: Amount) -> Receipt | Declined
                    constructs Receipt""", string(charge, "signature"));
        assertEquals("implemented", string(charge, "implementation"),
                "charge has a let, so nothing injects it");
    }

    /** Three words and not a flag: which of the two body-less states a behavior is in cannot be
     * worked out again from what is published, because the `let` that decides is not. */
    @Test
    void aBehaviorWithNoLetCarriesWhichOfTheTwoStatesItIsIn() {
        Map<String, byte[]> classes = Compiler.compile("""
                module shared.ledger exposing ( Entry, record, audited )
                data Entry = { amount: Int }
                behavior record : (e: Entry) -> Entry
                behavior audited : (e: Entry) -> Entry
                    depends on record
                """);

        assertEquals("injected",
                string(annotation(classes, "shared.ledger.Record", "SoutherBehavior"),
                        "implementation"));
        assertEquals("unimplemented",
                string(annotation(classes, "shared.ledger.Audited", "SoutherBehavior"),
                        "implementation"));
    }

    @Test
    void theModuleClassNamesWhatToRead() {
        Map<String, byte[]> classes = Compiler.compile(UP);

        Annotation module = annotation(classes, Emitted.declarations("shared.money"), "SoutherModule");
        assertEquals("shared.money", string(module, "name"));
        assertEquals(souther.compiler.codegen.Backend.BOUNDARY_VERSION, integer(module, "compat"));
        assertEquals("module shared.money exposing ( Amount, charge )", string(module, "header"));
        assertEquals(List.of("Amount", "Receipt", "Declined"), strings(module, "types"));
        assertEquals(List.of("charge"), strings(module, "behaviors"));
        assertEquals(List.of("import String ( length )"), strings(module, "imports"));
    }

    /** An invariant is part of what the type is, so the helpers it calls travel with it. A helper no
     * invariant reaches is the module's own business and stays behind. */
    @Test
    void onlyTheHelpersAnInvariantReachesAreCarried() {
        Map<String, byte[]> classes = Compiler.compile(UP);

        assertEquals(List.of("let withinCap (n: Int) = n <= 1000000"),
                strings(annotation(classes, Emitted.declarations("shared.money"), "SoutherModule"),
                        "invariantHelpers"));
    }

    /** What a clause reaches is read off the names it resolved to. A parameter is a binding, so a
     *  helper it happens to be spelled like is not one this declaration needs. */
    @Test
    void aParameterSpelledLikeAHelperDoesNotCarryIt() {
        Map<String, byte[]> classes = Compiler.compile("""
                module shadow.helper exposing ( echo )

                let positive (n: Int) = n > 0

                behavior echo : (positive: Int) -> Int
                    ensures value == positive
                let echo (positive) = positive
                """);

        assertEquals(List.of(),
                strings(annotation(classes, Emitted.declarations("shadow.helper"), "SoutherModule"),
                        "invariantHelpers"));
    }

    /**
     * And a behavior's body never crosses, whatever is spelled like it.
     *
     * <p>The strongest form of the same rule: an implementation is not part of what a reader of the
     * declarations needs, so a parameter sharing a behavior's name must not carry that behavior's
     * `let` — nor, through it, the helpers only the implementation reaches.
     */
    @Test
    void aParameterSpelledLikeABehaviorDoesNotCarryItsImplementation() {
        Map<String, byte[]> classes = Compiler.compile("""
                module shadow.impl exposing ( echo )

                behavior calculate : (x: Int) -> Int
                let calculate (x) = implementationOnly(x)

                let implementationOnly (n: Int) = n + 1

                behavior echo : (calculate: Int) -> Int
                    ensures value == calculate
                let echo (calculate) = calculate
                """);

        assertEquals(List.of(),
                strings(annotation(classes, Emitted.declarations("shadow.impl"), "SoutherModule"),
                        "invariantHelpers"),
                "an implementation does not cross the boundary, and neither does what only it reaches");
    }

    /** A helper a clause really calls is carried, since a reader cannot read the clause without it. */
    @Test
    void theHelperAClauseCallsIsCarried() {
        Map<String, byte[]> classes = Compiler.compile("""
                module carries.helper exposing ( echo )

                let doubled (n: Int) = n * 2

                behavior echo : (x: Int) -> Int
                    ensures value == doubled(x)
                let echo (x) = doubled(x)
                """);

        assertEquals(List.of("let doubled (n: Int) = n * 2"),
                strings(annotation(classes, Emitted.declarations("carries.helper"), "SoutherModule"),
                        "invariantHelpers"));
    }

    /**
     * What is carried is what the model declares.
     *
     * <p>An attached file's values join the module its rows join, so the module as resolved holds
     * `let`s an {@code examples for} file wrote. An attached file adds nothing to what the model
     * compiles to and there is nothing of it in a jar of the model, so a `let` only it declares is
     * not the module's to publish.
     *
     * <p>Asked of the definition, which says what it was made as. Answered by whether a slice of
     * its text happened to be kept, the set would come out right for a reason that is about how a
     * jar is written — and a definition of the module's own that some other pass had not kept a
     * slice for would drop out of what is published without anything saying so.
     *
     * <p>Nothing the model writes reaches such a value — that is refused where a name is answered
     * (spec §an-attached-files-values-are-for-its-rows) — so what this holds is the walk's own
     * domain rather than a second gate on the same mistake: a rule whose text is not the module's
     * is not published, whatever reaches it.
     */
    @Test
    void aValueOnlyAnAttachedFileDeclaresIsNotCarried() {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module beside.rows exposing ( Amount, echo )

                data Amount = { n: Int }
                    invariant n >= 0

                behavior echo : (x: Amount) -> Amount
                let echo (x) = x
                """, """
                examples for beside.rows

                let floor = Amount { n = 0 }

                example echo
                    | "unchanged" : (floor) -> floor
                """));

        assertEquals(List.of(),
                strings(annotation(classes, Emitted.declarations("beside.rows"), "SoutherModule"),
                        "invariantHelpers"),
                "the attached file's source is not in this module's jar, so it has none to carry");
    }

    /** A composition declares stages, not a signature. The importing module reads a signature, so
     * the computed one is written out and the stages stay behind. */
    @Test
    void aCompositionPublishesTheSignatureItComputesTo() {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module shop.pricing exposing ( Cart, Priced, quote )
                data Cart = { n: Int }
                data Priced = { total: Int }
                behavior quote : (c: Cart) -> Priced constructs Priced
                let quote (c) = Priced { total = c.n }
                """, """
                module shop.checkout exposing ( Done, place, checkout : Done )
                import shop.pricing ( Cart, Priced, quote )
                data Done = { total: Int }
                behavior place : (p: Priced) -> Done constructs Done
                let place (p) = Done { total = p.total }
                behavior checkout = quote >-> place
                """));

        assertEquals("behavior checkout : (in0: Cart) -> Done",
                string(annotation(classes, "shop.checkout.Checkout", "SoutherBehavior"), "signature"),
                "written in the names shop.checkout has: Cart came in on its import line and Done is"
                        + " its own");
    }

    private static Annotation annotation(Map<String, byte[]> classes, String binaryName,
                                         String simpleAnnotationName) {
        byte[] bytes = classes.get(binaryName);
        assertTrue(bytes != null, binaryName + " was not generated; got " + classes.keySet());
        for (RuntimeInvisibleAnnotationsAttribute attr : ClassFile.of().parse(bytes)
                .findAttributes(java.lang.classfile.Attributes.runtimeInvisibleAnnotations())) {
            for (Annotation a : attr.annotations()) {
                if (a.className().stringValue().endsWith("/" + simpleAnnotationName + ";")) {
                    return a;
                }
            }
        }
        throw new AssertionError(binaryName + " carries no @" + simpleAnnotationName);
    }

    private static AnnotationValue member(Annotation a, String name) {
        for (AnnotationElement e : a.elements()) {
            if (e.name().stringValue().equals(name)) {
                return e.value();
            }
        }
        throw new AssertionError("no member `" + name + "`");
    }

    private static String string(Annotation a, String name) {
        return ((AnnotationValue.OfString) member(a, name)).stringValue();
    }

    private static int integer(Annotation a, String name) {
        return ((AnnotationValue.OfInt) member(a, name)).intValue();
    }

    private static List<String> strings(Annotation a, String name) {
        List<String> out = new ArrayList<>();
        for (AnnotationValue v : ((AnnotationValue.OfArray) member(a, name)).values()) {
            out.add(((AnnotationValue.OfString) v).stringValue());
        }
        return out;
    }
}
