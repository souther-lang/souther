package souther.compiler.check;

import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.query.Shapes;

import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a test hands a reading of a declaration's rules.
 *
 * <p>The same answer the compilation gives itself, asked the same way. A test that built one out of
 * a scope and an empty representation would be reading the tree the backend emits from and calling
 * it the declaration's rules, which is the reading these tests are about.
 */
public final class RuleReadings {

    private RuleReadings() {}

    /** The reading {@code module} is read under in {@code compilation}. */
    public static RuleReadingSource of(Compilation compilation, String module) {
        return of(compilation.db(), module);
    }

    /** The reading of the one module {@code source} writes, for a test that has the text and no
     *  compilation of its own. */
    public static RuleReadingSource ofSource(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        return of(compilation, compilation.modules().get(0));
    }

    /** The same, for a test that holds the database rather than the compilation. */
    public static RuleReadingSource of(Db db, String module) {
        RuleReadingSource source = Shapes.ruleReading(db, module).value();
        assertNotNull(source, "no reading of `" + module + "`'s rules");
        return source;
    }

    /** A reading over a scope that declares nothing, for a test that writes no model. There is no
     *  declaration for a clause to be read off, so asking this for one is asking about a
     *  declaration that is not there. */
    public static RuleReadingSource ofNothingDeclared(Symbols symbols) {
        return new RuleReadingSource(symbols, nothingDeclared(symbols));
    }

    /** The clause representation of a scope that declares nothing. */
    public static AnalysisInvariants nothingDeclared(Symbols symbols) {
        return new AnalysisInvariants(symbols.module(), java.util.Map.of());
    }

    /** The clause representation {@code module} is read in, for a test that holds a scope of its
     *  own beside it. */
    public static AnalysisInvariants declaredBy(Db db, String module) {
        return of(db, module).invariants();
    }
}
