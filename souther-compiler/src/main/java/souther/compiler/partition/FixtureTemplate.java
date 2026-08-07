package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.TypeName;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * A value written the way a row writes it — {@code Amount(0)}, {@code None}, {@code Overseas} — held
 * both as the text a person reads and as the tree a decoder builds.
 *
 * <p>Two forms of one value, because the two questions asked of it are different. What goes into a
 * generated row is text, and only text: the row is printed for someone to complete, so nothing about
 * it is a built object. Whether it can be built at all is a different question, and the only honest way
 * to answer it is to build it, which needs the tree. Deriving one from the other would mean either a
 * parser for the text or a printer for what a decoder saw, and both would be a second spelling of the
 * same value with its own way of disagreeing.
 *
 * <p>The tree carries what its names denote, because that is what a fixture is read by. A construction
 * is reached by the type it names, not by the spelling — so the type is put there when the value is
 * made, where it is known, rather than looked up again from the text.
 */
public record FixtureTemplate(String text, Ast.Expr value) {

    /** Nothing generated is anywhere, and a fixture built here is never quoted back at a source. */
    private static final SourcePos NOWHERE = new SourcePos(0, 0);

    public FixtureTemplate {
        if (text == null || text.isBlank()) {
            throw new IllegalArgumentException("a fixture template is written text");
        }
    }

    public static FixtureTemplate integer(long value) {
        Ast.Expr magnitude = new Ast.IntLit(Math.abs(value), NOWHERE);
        return new FixtureTemplate(Long.toString(value),
                value < 0 ? new Ast.Neg(magnitude, NOWHERE) : magnitude);
    }

    public static FixtureTemplate decimal(BigDecimal value) {
        String written = value.stripTrailingZeros().toPlainString();
        BigDecimal magnitude = value.abs();
        Ast.Expr literal = new Ast.DecimalLit(magnitude, NOWHERE);
        return new FixtureTemplate(written + "m",
                value.signum() < 0 ? new Ast.Neg(literal, NOWHERE) : literal);
    }

    /**
     * A string, written the way the language reads one back.
     *
     * <p>Every escape a string literal has, because a row is offered as text to paste into a model and
     * has to come back as the value it was made from. A tab or a newline written as itself would end
     * the line the row is on as well.
     */
    public static FixtureTemplate string(String value) {
        StringBuilder written = new StringBuilder("\"");
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            switch (c) {
                case '\\' -> written.append("\\\\");
                case '"' -> written.append("\\\"");
                case '\n' -> written.append("\\n");
                case '\t' -> written.append("\\t");
                case '\r' -> written.append("\\r");
                default -> written.append(c);
            }
        }
        return new FixtureTemplate(written.append('"').toString(), new Ast.StringLit(value, NOWHERE));
    }

    public static FixtureTemplate bool(boolean value) {
        return new FixtureTemplate(Boolean.toString(value), new Ast.BoolLit(value, NOWHERE));
    }

    /** A date, written the way a row writes one: the constructor applied to an ISO 8601 string. */
    public static FixtureTemplate date(String iso) {
        return new FixtureTemplate("Date(\"" + iso + "\")",
                new Ast.Apply("Date", List.of(new Ast.StringLit(iso, NOWHERE)), NOWHERE));
    }

    public static FixtureTemplate dateTime(String iso) {
        return new FixtureTemplate("DateTime(\"" + iso + "\")",
                new Ast.Apply("DateTime", List.of(new Ast.StringLit(iso, NOWHERE)), NOWHERE));
    }

    /** The absent optional, which the language names rather than any module. */
    public static FixtureTemplate none() {
        return new FixtureTemplate("None",
                new Ast.Var("None", new ValueName.Builtin("None"), new ReachName.Bare("None"),
                        NOWHERE));
    }

    /** A case that carries nothing: naming it is constructing it. */
    public static FixtureTemplate unitCase(TypeName type) {
        return new FixtureTemplate(type.name(), new Ast.Var(type.name(),
                new ValueName.OfType(type.name(), type, ConstructionOrigin.own()),
                new ReachName.Bare(type.name()), NOWHERE));
    }

    /** A newtype around one value, written in the call form a row writes it in (ADR-0032). */
    public static FixtureTemplate newtype(TypeName type, FixtureTemplate inner) {
        return new FixtureTemplate(type.name() + "(" + inner.text() + ")",
                new Ast.Apply(type.name(), List.of(inner.value()), NOWHERE));
    }

    /** No elements. A list, a set and a map are all written this way in a fixture: what the position
     * is decides what the empty brackets become. */
    public static FixtureTemplate emptyCollection() {
        return new FixtureTemplate("[]", new Ast.ListLit(List.of(), NOWHERE));
    }

    /** A record, field by field, in the order the fields were declared. */
    public static FixtureTemplate record(TypeName type, Map<String, FixtureTemplate> fields) {
        List<String> written = new ArrayList<>();
        List<Ast.FieldInit> inits = new ArrayList<>();
        for (Map.Entry<String, FixtureTemplate> field : fields.entrySet()) {
            written.add(field.getKey() + " = " + field.getValue().text());
            inits.add(new Ast.FieldInit(field.getKey(), field.getValue().value(), NOWHERE));
        }
        return new FixtureTemplate(type.name() + " { " + String.join(", ", written) + " }",
                new Ast.NewData(Ast.Name.resolved(type, NOWHERE), inits, List.of(),
                        ConstructionOrigin.own(), NOWHERE));
    }
}
