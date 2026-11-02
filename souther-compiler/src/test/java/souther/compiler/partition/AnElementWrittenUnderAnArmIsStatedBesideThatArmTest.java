package souther.compiler.partition;

import net.unit8.notation199x.pattern.PatternMeaning;
import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.PieceWitness;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.StringsLanguage;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.semantics.CaseMapping;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ValueName;

import java.lang.reflect.RecordComponent;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.OptionalInt;
import java.util.OptionalLong;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * That some element of a list a closure wrote under one arm meets a statement is that the arm is
 * taken for a piece and the statement holds of the piece, together.
 */
class AnElementWrittenUnderAnArmIsStatedBesideThatArmTest {

    private static final String ATTEMPT = """
            List.length(List.flatMap(n -> List.filter(a -> a.name == n.value, rows),
                    List.flatMap(d -> if Letters(d) as n then [ n ] else [ ],
                                 String.split("@", s)))) >= 1""";

    private static Proposition.InTheStrings held(PieceWitness of, String text) {
        return new Proposition.InTheStrings(new Proposition.InTheStrings.Strings.OfAPiece(of),
                new StringsLanguage(PatternMeaning.text(text)), true);
    }

    /**
     * Two statements about some piece that follow each other are two statements, however deep
     * each is read: what they say of their pieces is not one statement's, so the pieces are told
     * apart by the statement and not by the depth, in what is stated and in how it is spelled.
     */
    @Test
    void twoStatementsAtOneDepthAreAboutTwoPieces() {
        PieceWitness first = at(0, 0);
        PieceWitness second = at(0, 1);
        assertNotEquals(held(first, "ab"), held(second, "ab"));
        assertNotEquals(held(first, "ab").spelling(), held(second, "ab").spelling());
        assertEquals(held(first, "ab"), held(at(0, 0), "ab"));
    }

    /** The piece the closure parameter number {@code parameter} stands for, {@code depth} in. */
    private static PieceWitness at(int depth, int parameter) {
        return new PieceWitness(depth, new PieceWitness.Site.Parameter(
                new BindingId(new BindingOwner.OfValue("demo", "f"), parameter)));
    }

    /** And the piece of a comparison is the piece of the statement it is read in. */
    @Test
    void aPieceReadInTwoStatementsIsTwoValues() {
        Quantity string = new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("s")));
        ValueName.Stdlib split = ValueName.Stdlib.operation("String", "split");
        Quantity.APieceOf first = new Quantity.APieceOf(split, OptionalInt.of('@'), string,
                at(0, 0), 0, 0);
        Quantity.APieceOf second = new Quantity.APieceOf(split, OptionalInt.of('@'), string,
                at(0, 1), 0, 0);
        assertNotEquals(first, second);
        assertNotEquals(first.spelling(), second.spelling());
    }

    /** A count of the pieces of {@code of}, parted at {@code at}, that {@code type} builds and rows name. */
    private static String counted(String type, String bound, String at, String of) {
        return counted(type, bound, at, of, "rows");
    }

    private static String counted(String type, String bound, String at, String of, String rows) {
        return "List.length(List.flatMap(" + bound + " -> List.filter(a -> a.name == " + bound
                + ".value, " + rows + "), List.flatMap(d -> if " + type + "(d) as " + bound
                + " then [ " + bound + " ] else [ ], String.split(\"" + at + "\", " + of
                + ")))) >= 1";
    }

    /**
     * The statements about some piece the pieces held to a language were read in, as each says
     * which it is, taken from the steps the reading met.
     */
    private static Set<PieceWitness> statementsAboutSomePiece(Pullback.Pulled pulled) {
        Set<PieceWitness> out = new LinkedHashSet<>();
        for (Pullback.Leaf leaf : pulled.leaves()) {
            heldToALanguageIn(leaf.step(), out);
        }
        return out;
    }

    /**
     * Every piece held to a language in {@code derivation}, however it is put together: found by
     * what a step is, and not by how it prints or in which order it holds its parts.
     */
    private static void heldToALanguageIn(Object derivation, Set<PieceWitness> into) {
        switch (derivation) {
            case Derivation.APieceInALanguage held -> into.add(held.within());
            case Record record -> {
                for (RecordComponent component : record.getClass().getRecordComponents()) {
                    try {
                        component.getAccessor().setAccessible(true);
                        heldToALanguageIn(component.getAccessor().invoke(record), into);
                    } catch (ReflectiveOperationException broken) {
                        throw new IllegalStateException(broken);
                    }
                }
            }
            case Iterable<?> parts -> parts.forEach(part -> heldToALanguageIn(part, into));
            case Optional<?> maybe -> maybe.ifPresent(part -> heldToALanguageIn(part, into));
            case null, default -> { }
        }
    }

    /** One statement about some piece is one piece, however many parts it is read in. */
    @Test
    void oneQuantifierIsOneStatementAboutSomePiece() {
        assertEquals(1, statementsAboutSomePiece(pulled(counted("Letters", "n", "@", "s"))).size());
    }

    /**
     * Two quantifiers over the same pieces are two statements: the pieces are the same set and
     * the witnesses are two, so what one says of its piece is not said of the other's.
     */
    @Test
    void twoQuantifiersOverOneSplitAreTwoStatementsAboutSomePiece() {
        Set<PieceWitness> statements = statementsAboutSomePiece(pulled(
                counted("Letters", "n", "@", "s") + " && " + counted("Letters", "m", "@", "s")));
        assertEquals(2, statements.size(), statements::toString);
    }

    /** And over two strings. */
    @Test
    void twoQuantifiersOverTwoStringsAreTwoStatementsAboutSomePiece() {
        Set<PieceWitness> statements = statementsAboutSomePiece(pulled(
                counted("Letters", "n", "@", "s") + " && " + counted("Digits", "m", "#", "t")));
        assertEquals(2, statements.size(), statements::toString);
    }

    /** One helper applied to two strings is two statements, one for each call. */
    @Test
    void oneHelperAppliedTwiceIsTwoStatementsAboutSomePiece() {
        String helper = "let named (x: String, rs: List<Row>): Bool = "
                + counted("Letters", "n", "@", "x", "rs") + "\n";
        Set<PieceWitness> statements = statementsAboutSomePiece(pulled(helper,
                "named(s, rows) && named(t, rows)"));
        assertEquals(2, statements.size(), statements::toString);
    }

    /**
     * The closure parameter that stands for a piece is a different binding in each application of
     * a helper, so the pieces of two applications are told apart by it where no quantifier call
     * names them.
     */
    @Test
    void theParameterOfAHelperIsAnotherBindingInEachApplication() {
        String helper = "let named (x: String, rs: List<Row>): Bool = "
                + counted("Letters", "n", "@", "x", "rs") + "\n";
        Set<BindingId> bindings = new LinkedHashSet<>();
        collectReadsNamed("d", analysisOf(helper, "named(s, rows) && named(t, rows)").core(),
                bindings);
        assertEquals(2, bindings.size(), bindings::toString);
    }

    private static void collectReadsNamed(String name, Core e, Set<BindingId> into) {
        Core written = Core.withoutStanding(e);
        if (written instanceof Core.Read read && read.name().equals(name)
                && read.binding() != null) {
            into.add(read.binding());
        }
        Core.forEachChild(written, child -> collectReadsNamed(name, child, into));
    }

    /**
     * A call the source did not write is every such call, one occurrence that names no statement:
     * it is no site, and a quantifier standing at it is not read.
     */
    @Test
    void aQuantifierTheSourceDidNotWriteIsNoSite() {
        assertEquals(null, PieceWitness.Site.quantifiedAt(ConstructOccurrence.unwritten()));
        assertEquals(null, PieceWitness.Site.quantifiedAt(null));
        assertThrows(IllegalArgumentException.class,
                () -> new PieceWitness.Site.Quantifier(ConstructOccurrence.unwritten()));
    }

    /**
     * What is said of where a piece comes from is one thing: statements that disagree are about
     * no piece, and nothing is taken of it.
     */
    @Test
    void statementsThatDisagreeOnWhereAPieceComesFromGiveNoString() {
        PieceWitness piece = at(0, 0);
        Derivation.APieceInALanguage fromS = held(piece, "ab", "s");
        Derivation.APieceInALanguage fromT = held(piece, "ab", "t");
        PartedStringsOfThePieces agreed = PartedStringsOfThePieces.of(List.of(fromS, fromS));
        assertEquals(fromS.parted(), agreed.of(piece));
        PartedStringsOfThePieces disagreed = PartedStringsOfThePieces.of(List.of(fromS, fromT));
        assertEquals(Optional.empty(), disagreed.of(piece));
    }

    /** Pieces at one depth that are two statements' keep each its own string. */
    @Test
    void piecesAtOneDepthKeepTheStringsOfTheirOwnStatements() {
        PartedStringsOfThePieces strings = PartedStringsOfThePieces.of(List.of(
                held(at(0, 0), "ab", "s"), held(at(0, 1), "12", "t")));
        assertEquals(held(at(0, 0), "ab", "s").parted(), strings.of(at(0, 0)));
        assertEquals(held(at(0, 1), "12", "t").parted(), strings.of(at(0, 1)));
    }

    private static Derivation.APieceInALanguage held(PieceWitness of, String text, String string) {
        return new Derivation.APieceInALanguage(new StringsLanguage(PatternMeaning.text(text)),
                "String.matches", text, of, Optional.of(
                        new Derivation.APieceInALanguage.PartedString(TermPath.of(string),
                                CaseMapping.NONE, '@', 0, OptionalLong.empty())));
    }

    private static List<Proposition> partsOfWhatSomeRowMeets(Proposition stated) {
        Proposition.Some some = assertInstanceOf(Proposition.Some.class, stated);
        assertEquals("rows", some.container().toString().replaceAll(".*?(rows).*", "$1"));
        return assertInstanceOf(Proposition.All.class, some.ofTheElement()).parts();
    }

    /**
     * Some row has the name of a piece the attempt builds a value of: the row's name is one of the
     * pieces, and it is in the language the attempt builds, both of the one row. Without the
     * language the statement would be about a piece the attempt does not build.
     */
    @Test
    void theArmBeingTakenIsStatedBesideTheRowBeingAPiece() {
        List<Proposition> parts = partsOfWhatSomeRowMeets(stated(ATTEMPT));
        assertEquals(2, parts.size(), parts::toString);
        assertInstanceOf(Proposition.Compared.class, parts.get(0));
        Proposition.InTheStrings language = assertInstanceOf(Proposition.InTheStrings.class,
                parts.get(1));
        assertEquals(true, language.holds());
        assertEquals(Proposition.InTheStrings.Strings.AtAPosition.class,
                language.of().getClass());
        assertEquals(true, language.accepts().toString().contains("0061-007A"),
                language::toString);
    }


    /** What the condition of the fork on {@code truth} states. */
    private static Proposition stated(String truth) {
        return pulled(truth).proposition();
    }

    /** What the condition of the fork on {@code truth} was read as. */
    private static Pullback.Pulled pulled(String truth) {
        return pulled("", truth);
    }

    /** What the condition of the fork on {@code truth} was read as, with {@code lets} before it. */
    private static Pullback.Pulled pulled(String lets, String truth) {
        Compilation compilation = compiled(lets, truth);
        AnalysisBody analysis = analysisOf(compilation);
        RuleReadingSource rules = RuleReadings.of(compilation, "p");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("p")).value().get("f");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        Core e = Core.withoutStanding(analysis.core());
        while (e instanceof Core.LetIn let) {
            reads = reads.and(let.binder(), let.value());
            e = Core.withoutStanding(let.body());
        }
        Core.If fork = assertInstanceOf(Core.If.class, e, "the body is one fork");
        return Pullback.ofATruth(fork.cond(), reads, inputs.reading(rules), Optional.empty());
    }

    private static AnalysisBody analysisOf(String lets, String truth) {
        return analysisOf(compiled(lets, truth));
    }

    private static AnalysisBody analysisOf(Compilation compilation) {
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("p")).value();
        return checked.analysisBodies().get("f");
    }

    private static Compilation compiled(String lets, String truth) {
        String source = """
                module p
                data Letters = String
                    invariant String.matches("[a-z]+", value)
                data Digits = String
                    invariant String.matches("[0-9]+", value)
                data Word = String
                    invariant String.matches("[a-z0-9]+", value)
                data Row = { name: String }
                data Yes
                data No
                behavior f : (s: String, t: String, rows: List<Row>, r: Word, u: Word)
                        -> Yes | No
                    constructs %s
                %s
                let f (s, t, rows, r, u) = if %s then Yes else No
                """.formatted(truth.contains("Digits(") || lets.contains("Digits(")
                        ? "Letters, Digits" : "Letters", lets, truth);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return compilation;
    }
}
