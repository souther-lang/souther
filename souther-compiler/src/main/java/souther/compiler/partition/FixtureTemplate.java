package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.ast.WrittenName;
import souther.compiler.check.Carrier;
import souther.compiler.diag.Region;
import souther.compiler.numeric.Count;
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

    /** And nothing generated was written over anything: a row is text this builds, not text anyone
     *  typed, so there is no stretch of any file to underline. */
    private static final Region NO_SOURCE = null;

    public FixtureTemplate {
        if (text == null || text.isBlank()) {
            throw new IllegalArgumentException("a fixture template is written text");
        }
    }

    public static FixtureTemplate integer(long value) {
        Ast.Expr magnitude = new Ast.IntLit(Math.abs(value), NOWHERE, NO_SOURCE);
        return new FixtureTemplate(Long.toString(value),
                value < 0 ? new Ast.Neg(magnitude, NOWHERE, NO_SOURCE) : magnitude);
    }

    public static FixtureTemplate decimal(BigDecimal value) {
        String written = value.stripTrailingZeros().toPlainString();
        BigDecimal magnitude = value.abs();
        Ast.Expr literal = new Ast.DecimalLit(magnitude, NOWHERE, NO_SOURCE);
        return new FixtureTemplate(written + "m",
                value.signum() < 0 ? new Ast.Neg(literal, NOWHERE, NO_SOURCE) : literal);
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
        return new FixtureTemplate(written.append('"').toString(), new Ast.StringLit(value, NOWHERE, NO_SOURCE));
    }

    public static FixtureTemplate bool(boolean value) {
        return new FixtureTemplate(Boolean.toString(value), new Ast.BoolLit(value, NOWHERE, NO_SOURCE));
    }

    /** A date, written the way a row writes one: the constructor applied to an ISO 8601 string. */
    public static FixtureTemplate date(String iso) {
        return new FixtureTemplate("Date(\"" + iso + "\")",
                new Ast.Apply("Date", List.of(new Ast.StringLit(iso, NOWHERE, NO_SOURCE)),
                        NOWHERE, NO_SOURCE));
    }

    public static FixtureTemplate dateTime(String iso) {
        return new FixtureTemplate("DateTime(\"" + iso + "\")",
                new Ast.Apply("DateTime", List.of(new Ast.StringLit(iso, NOWHERE, NO_SOURCE)),
                        NOWHERE, NO_SOURCE));
    }

    /** The absent optional, which the language names rather than any module. */
    public static FixtureTemplate none() {
        return new FixtureTemplate("None",
                new Ast.Var(WrittenName.synthetic("None", NOWHERE),
                        new ValueName.Builtin("None"), new ReachName.Bare("None")));
    }

    /** A case that carries nothing: naming it is constructing it. */
    public static FixtureTemplate unitCase(TypeName type) {
        return new FixtureTemplate(type.name(),
                new Ast.Var(WrittenName.synthetic(type.name(), NOWHERE),
                        new ValueName.OfType(type.name(), type, ConstructionOrigin.own()),
                        new ReachName.Bare(type.name())));
    }

    /** A newtype around one value, written in the call form a row writes it in (ADR-0032). */
    /**
     * A count written as the value it stands for, wrapped where the position wears a name.
     *
     * <p>The one place a count becomes something a row carries. Which literal a count is written as
     * is the carrier's answer and is taken from it — spelled out per caller instead, a date-time's
     * second count reached a row as an {@code Int}, and the decoder turned it down with nothing said
     * about why.
     *
     * @param wrapper the single-value newtype the position is declared as, or null for a bare value
     */
    public static FixtureTemplate on(Carrier carrier, Count at, TypeName wrapper) {
        FixtureTemplate literal = switch (carrier) {
            case WHOLE -> integer(at.at().longValueExact());
            case DENSE -> decimal(at.at());
            // Written by the carrier, so the text on a row and the text in a report are the same
            // text. Spelled here as well, the two could differ at midnight and nowhere else.
            case DATE -> date(carrier.written(at));
            case MOMENT -> dateTime(carrier.written(at));
        };
        return wrapper == null ? literal : newtype(wrapper, literal);
    }

    public static FixtureTemplate newtype(TypeName type, FixtureTemplate inner) {
        return new FixtureTemplate(type.name() + "(" + inner.text() + ")",
                new Ast.Apply(type.name(), List.of(inner.value()), NOWHERE, NO_SOURCE));
    }

    /** No elements. A list, a set and a map are all written this way in a fixture: what the position
     * is decides what the empty brackets become. */
    public static FixtureTemplate emptyCollection() {
        return collection(List.of());
    }

    /**
     * A collection of what it holds, in the order the elements were chosen.
     *
     * <p>The same brackets for all three, for the same reason the empty one has them: a fixture writes
     * a set as its elements and a map as its entry pairs, and which of them the brackets are is what
     * the position declares rather than anything spelled here.
     */
    public static FixtureTemplate collection(List<FixtureTemplate> elements) {
        List<Ast.Expr> values = new ArrayList<>();
        List<String> written = new ArrayList<>();
        for (FixtureTemplate each : elements) {
            values.add(each.value());
            written.add(each.text());
        }
        return new FixtureTemplate("[" + String.join(", ", written) + "]",
                new Ast.ListLit(List.copyOf(values), NOWHERE, NO_SOURCE));
    }

    /** One entry of a map: the pair a fixture writes a key and its value as. */
    public static FixtureTemplate entry(FixtureTemplate key, FixtureTemplate value) {
        return new FixtureTemplate("(" + key.text() + ", " + value.text() + ")",
                new Ast.Tuple(List.of(key.value(), value.value()), NOWHERE, NO_SOURCE));
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
                        ConstructionOrigin.own(), NOWHERE, NO_SOURCE));
    }
}
