package souther.compiler.inputs;

import souther.compiler.ast.Hir;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.RuleAccounting;
import souther.compiler.check.ProjectionEvidence;
import souther.compiler.check.Rules;
import souther.compiler.check.Shape;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeView;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.values.AdmissibleSet;

import java.util.ArrayList;
import java.util.List;

/**
 * The value a position is inside: what it is called, and what its rules leave each position of it
 * able to hold.
 *
 * <p>One reading per parameter, not one per record met on the way down. A clause on the outer
 * record relates positions at any depth it can name, and rebuilding the reading at each record is
 * how {@code interval.startsAt < cap} stopped reaching {@code interval.startsAt}.
 */
record PlacedRules(TypeSymbol value, Rules rules) {

    /**
     * What the rules reaching a value of {@code type} leave and place, read under the name the
     * signature wrote.
     *
     * <p>The written name and not the record under it. A name wrapped round a record is a place the
     * same rule can be written — {@code data NonEmptyBag = Bag invariant List.length(value.xs) >= 1}
     * states what {@code Bag} could have stated about its own field — and reading the record alone
     * drops every clause of every name round it. What those clauses leave is read at the paths the
     * record's own positions have, since a name wrapped round a value is not a step of the path.
     *
     * <p>One reading and not two. A wrapper's clauses place ends, project ranges onto the record's
     * fields, and can be ones this could not read, and all three are answers about the same value:
     * lifted as ends alone, a wrapper relating two of the record's fields narrowed nothing and a
     * wrapper clause nothing could read left every edge under it looking certain.
     */
    static PlacedRules of(Type type, Symbols symbols) {
        TypeSymbol read = readAs(type, symbols);
        return new PlacedRules(read, Rules.of(read, symbols));
    }

    /** What the rules leave the numbers, ends and narrowings of this value. */
    FieldDomains bounds() {
        return rules.bounds();
    }

    /** What is left for the position at {@code path}, which is read from the value this is of. */
    NumericDomain.Bounds at(TermPath path) {
        return path.fields().isEmpty() ? null : bounds().at(String.join(".", path.fields()));
    }

    /**
     * Where the position at {@code path} stops once every rule reaching this value has been taken
     * in, which is not the same as what {@link #at} projects onto it.
     */
    NumericDomain.Bounds leftAt(TermPath path, boolean measured) {
        return bounds().leftAt(String.join(".", path.fields()), measured);
    }

    /**
     * Which values the position at {@code path} may hold, and how much of its rules was read.
     *
     * <p>Asked at every path, the value's own included: what a name wraps is at no path of its own
     * and is the position a reader of a newtype asks about, which is why this is not the empty
     * answer where {@link #at} is.
     */
    AdmissibleSet admits(TermPath path) {
        return rules.admits(String.join(".", path.fields()));
    }

    /**
     * The questions the rules reaching this value raise about the position at {@code path} that
     * nothing answered, each with the rule that raised it.
     *
     * <p>Asked of the questions and not of the readings. A reading being short of a position's
     * rules is a fact about that reading; whether a rule went unaccounted for is a fact about the
     * model, and the two come apart wherever one reading answers what another could not — which is
     * every bound on a number, since the reading that turns clauses into sets of values has no word
     * for a range.
     */
    List<RuleAccounting.Unanswered> unanswered(TermPath path) {
        String where = String.join(".", path.fields());
        List<RuleAccounting.Unanswered> out = new ArrayList<>();
        bounds().accounting().values().forEach(accounting ->
                accounting.unansweredQuestions().stream()
                        .filter(each -> each.owed().subject().path().equals(where))
                        .forEach(out::add));
        return List.copyOf(out);
    }

    /**
     * How much of what the rules say the bounds of this value are able to state.
     *
     * <p>Asked of the value and not of one position in it, because that is what it licenses: a row
     * at an edge is a whole value with that edge in it, so a rule the bounds cannot express is a way
     * that value can be refused however plainly the numbers beside it were read.
     */
    ProjectionEvidence projection() {
        return rules.projection();
    }

    /**
     * Whether the gathering reached every rule written about the position at {@code path}.
     *
     * <p>Asked of the gathering, which is what knows. A position can carry both a rule that arrived
     * and could not be read and a subtree the walk never entered, and what a reading came back
     * short of has one slot to answer in — so reach read off {@link #admits} is lost wherever
     * another reason won it.
     */
    boolean everyRuleReachedAt(TermPath path) {
        return rules.everyRuleReachedAt(String.join(".", path.fields()));
    }

    /** The ends the clauses reaching this value place on the coordinates at {@code path}, which is
     *  a different question from what {@link #at} leaves them. */
    List<FieldDomains.Placed> placedAt(TermPath path) {
        return path.fields().isEmpty() ? List.of()
                : bounds().placedAt(String.join(".", path.fields()));
    }

    /**
     * The rules saying where the coordinate at {@code path} stops that no end came out of.
     *
     * <p>At every path the value has, its own included — unlike {@link #placedAt}, whose empty
     * answer at the root is what the type's own reading already gives. A rule nothing could read is
     * not given twice by anybody, and a newtype's own clause is where the question started.
     */
    List<FieldDomains.Unread> unreadAt(TermPath path) {
        return bounds().unreadAt(String.join(".", path.fields()));
    }

    /** Which declarations' clauses are holding the end at {@code path}, on the side asked for. */
    List<TypeSymbol> narrowedBy(TermPath path, boolean lower) {
        return path.fields().isEmpty() ? List.of()
                : bounds().narrowedBy(String.join(".", path.fields()), lower);
    }

    /**
     * The declaration a value of {@code type} is read under: the name the signature wrote where it
     * names one, and the record beneath the names where it does not.
     *
     * <p>One name for both questions. Which declaration's rules reach the positions, and which
     * declaration is said to have taken an edge in, are answers about the same value — read apart,
     * an edge a wrapper narrowed was reported as narrowed by the record under it, which is a
     * declaration that may have no clause about the pair at all.
     */
    private static TypeSymbol readAs(Type type, Symbols symbols) {
        TypeSymbol written = nameOf(type);
        return written != null
                && symbols.declarations().declaration(written.key()) instanceof Hir.Data
                ? written : heldIn(type, symbols);
    }

    /**
     * The declaration whose rules reach the position: the record under the names where there is
     * one, and the declaration as written where there is not.
     *
     * <p>A position that is not a record has no fields for a clause to relate, and its own rules
     * still say what a reading of them could not turn into a range — which is what keeps an edge it
     * refuses from being called writable. So the answer falls back to the name the signature wrote
     * rather than to nothing.
     */
    private static TypeSymbol heldIn(Type type, Symbols symbols) {
        TypeSymbol record = recordIn(type, symbols);
        return record != null ? record : nameOf(type);
    }

    /** The record a position holds, through the names it is written under: a value of
     *  {@code data SlotN = Slot} is a {@code Slot}, and the clauses relating its fields are
     *  {@code Slot}'s. */
    private static TypeSymbol recordIn(Type type, Symbols symbols) {
        return TypeView.of(type, symbols).shape() instanceof Shape.Product product
                ? product.name() : null;
    }

    private static TypeSymbol nameOf(Type type) {
        return type instanceof Type.Ref ref ? ref.name() : null;
    }
}
