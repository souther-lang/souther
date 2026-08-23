package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.diag.msg.MessageValues;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Names;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * What a value of a type can be, when a case of it is itself a sum.
 *
 * <p>Four readers used to descend a sum's cases themselves — two in {@link TypeOps}, one keyed on
 * the declaration rather than the type, and one in the derivation keyed on the written name. Three
 * of them are held here against {@link LeafSpace}, which is the descent, and the fourth follows
 * (#990). What each of them answers <em>about</em> a type it was handed is its own and is held here
 * too: a reader asking {@code sumCases} is asking whether there are cases to read at all, and a
 * type that is its own one leaf is not that.
 */
class WhatATypeIsMadeOfIsAnsweredInOnePlaceTest {

    /** A sum two deep, and a leaf two of its cases reach. */
    private static final String MODULE = """
            module m

            data Station
            data Hospital
            data Clinic
            data Renkei
            data OnceKind   = Station | Hospital
            data Outpatient = Station | Clinic
            data VisitKind  = OnceKind | Renkei
            data Both       = OnceKind | Outpatient
            """;

    private final Hir.Module module = resolved(MODULE);
    private final Symbols symbols = TypeChecker.symbols(module);

    @Test
    void aCaseThatIsASumIsTheLeavesUnderIt() {
        assertEquals(List.of("Station", "Hospital", "Renkei"), shown(leavesOf("VisitKind")),
                "a value of the outer sum is one of the leaves, not one of the two cases");
    }

    /**
     * The declaration reaches {@code Station} through {@code OnceKind} and again through
     * {@code Outpatient}. It is one type, so it is one leaf, and it keeps the place it was first
     * reached at — the order a derived codec writes its variants in (spec §sum-discrimination).
     */
    @Test
    void aLeafReachedTwiceIsOneLeafWhereItWasFirstReached() {
        assertEquals(List.of("Station", "Hospital", "Clinic"), shown(leavesOf("Both")));
    }

    /**
     * The same where what two cases reach is a sum rather than a leaf.
     *
     * <p>Held apart from the leaf-level one because the descent stops differently: the second
     * reach of {@code N} is not descended at all, where the second reach of a leaf is descended
     * and discarded. What the two must agree on is that the leaves under it are contributed once,
     * where {@code N} was first reached.
     */
    @Test
    void aNestedSumReachedThroughTwoCasesContributesItsLeavesOnce() {
        Hir.Module shared = resolved("""
                module m

                data R
                data T
                data P
                data Q
                data N   = R | T
                data A   = N | P
                data B   = N | Q
                data Top = A | B
                """);
        assertEquals(List.of("R", "T", "P", "Q"),
                shown(LeafSpace.leavesOf(Type.ref(named(shared, "Top")), TypeChecker.symbols(shared))));
    }

    @Test
    void aTypeThatIsNoSumIsTheOneLeafItIs() {
        assertEquals(List.of("Station"), shown(leavesOf("Station")));
    }

    @Test
    void aUnionDescendsAMemberThatIsASum() {
        Type union = Type.union(Set.of(named("OnceKind"), named("Renkei")));
        assertEquals(Set.of("Station", "Hospital", "Renkei"),
                Set.copyOf(shown(LeafSpace.leavesOf(union, symbols))),
                "a member written as a sum contributes its leaves, as a declared case does");
    }

    /** A sum naming itself is refused where it is written; the descent only has to come back. */
    @Test
    void aSumReachingItselfComesBack() {
        Hir.Module itself = resolved("""
                module m

                data A
                data S = A | S
                """);
        assertEquals(List.of("A"),
                shown(LeafSpace.leavesOf(Type.ref(named(itself, "S")), TypeChecker.symbols(itself))));
    }

    /** What a sum declares, asked of the declaration — the same leaves, and its own name is not one. */
    @Test
    void aSumsOwnDeclarationAnswersWithTheSameLeaves() {
        Hir.SumData both = (Hir.SumData) declaration("Both");
        assertEquals(shown(leavesOf("Both")), shown(TypeOps.leafCases(both, symbols)));
    }

    // --- what each reader answers about a type that is no sum ------------------------------------

    @Test
    void askingForACasesToReadIsNotAnsweredByATypeThatIsItsOwnLeaf() {
        assertNull(TypeOps.sumCases(Type.ref(named("Station")), symbols),
                "a data with no cases has none to read, which is not the same as having itself");
        assertEquals(List.of("Station", "Hospital", "Renkei"),
                shown(TypeOps.sumCases(Type.ref(named("VisitKind")), symbols)));
    }

    @Test
    void aLeafSetAnswersForATypeThatIsNoSum() {
        assertEquals(List.of("Station"),
                shown(List.copyOf(TypeOps.leafCases(Type.ref(named("Station")), symbols))));
    }

    /**
     * Where the one answer that changed is seen from outside.
     *
     * <p>{@code sumCases} named a leaf once per path that reached it, and the cases without the
     * field are listed from what it answered, so a reader of a diamond was told about one case
     * twice. This is the only reader of that list, which is what makes the change to it this
     * small.
     */
    @Test
    void aCaseReachedTwiceIsNamedOnceInWhatHasNoSuchField() {
        souther.compiler.diag.CompileException refused = org.junit.jupiter.api.Assertions
                .assertThrows(souther.compiler.diag.CompileException.class,
                        () -> souther.compiler.Compiler.compile(MODULE + """

                                let f (b: Both) : Int = b.x
                                """));
        assertEquals("E1321", refused.diagnostic().code());
        assertEquals(List.of("Station, Hospital, Clinic"),
                refused.diagnostic().notes().stream()
                        .map(n -> String.valueOf(MessageValues.of(n.said()).get("cases")))
                        .toList());
    }

    @Test
    void anOutputsCasesAreEmptyWhereTheOutputNamesNoCase() {
        assertEquals(Set.of(), TypeOps.outputCases(Type.INT, symbols),
                "a primitive output is not a case list, whatever leaf its name would be");
    }

    // --- helpers ---------------------------------------------------------------------------------

    private List<TypeSymbol> leavesOf(String type) {
        return LeafSpace.leavesOf(Type.ref(named(type)), symbols);
    }

    private TypeSymbol named(String type) {
        return named(module, type);
    }

    private static TypeSymbol named(Hir.Module m, String type) {
        return declarationIn(m, type).declares();
    }

    private Hir.Def declaration(String type) {
        return declarationIn(module, type);
    }

    private static Hir.Def declarationIn(Hir.Module m, String type) {
        for (Hir.Def d : m.defs()) {
            if (d.name().equals(type)) {
                return d;
            }
        }
        throw new AssertionError("the module does not declare " + type);
    }

    private static List<String> shown(List<TypeSymbol> names) {
        return names.stream().map(TypeSymbol::name).toList();
    }

    private static Hir.Module resolved(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("m.sou", source);
        return Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY)
                .db().ask(new Names.Resolved("m")).value();
    }
}
