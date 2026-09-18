package souther.compiler.check;

import souther.compiler.core.ValueShape;
import souther.compiler.observe.Composed;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What this compile settled its declarations are made of.
 *
 * <p>The accepted program's reading, and the only one anything running its rows may have. What a
 * value of a declaration is made of is decided once, where the declaration is checked
 * ({@link ExecutableInvariants}); this hands that decision over and re-reads nothing. So a row
 * compared against a field and a text typed by the same field are held to one answer, and the JVM
 * refusing a construction is refusing it by that answer too.
 *
 * <p>Which shape to hand over is asked by the declaration's own identity, and a declaration this
 * compile resolved has one. Three ways of not having one, and each is said as what it is: a name
 * nothing declares, a declaration this reading cannot reach what it says of, and one it reaches
 * that the check settled nothing about. None of them is a data with no fields.
 */
public final class CheckedDeclarations implements souther.compiler.observe.Declarations {

    /** What each declaration was checked to be, asked for by the declaration's own identity. */
    public interface Shapes {

        /** What a value of {@code declared} is made of, or null where this compile settled nothing
         *  about it. */
        ValueShape of(TypeSymbol.AtModule declared);
    }

    private final PublishedDeclarations published;
    private final Shapes shapes;

    public CheckedDeclarations(PublishedDeclarations published, Shapes shapes) {
        if (published == null || shapes == null) {
            throw new IllegalArgumentException("a checked declaration is what a module wrote and"
                    + " what the check said about it: " + published + " " + shapes);
        }
        this.published = published;
        this.shapes = shapes;
    }

    @Override
    public Composed of(TypeSymbol.AtModule declared) {
        // What the declaration says, and not the tree the module that wrote it holds. Which of the
        // three it is, is the whole of what is read here, and where it was written is not among the
        // answers — so a declaration moved in its file leaves every row read against it alone.
        return switch (published.of(declared.key())) {
            case PublishedDeclarationResult.Found(DeclarationMeaning.Product _) ->
                    new Composed.OfFields(fieldsOf(declared));
            case PublishedDeclarationResult.Found _ -> Composed.NOTHING;
            // A module wrote this one and this reading cannot see what it says. Said as what it is:
            // a declaration out of reach is not a declaration with nothing under it.
            case PublishedDeclarationResult.Unavailable _ ->
                    throw new IllegalStateException("`" + declared + "` is declared by a module"
                            + " and this reading cannot reach what it declares");
            // And which shape to hand over is asked by a declaration's own identity, which this
            // compile made. A name it has no declaration of arriving here is this compiler handing
            // over an identity for a declaration it does not have.
            case PublishedDeclarationResult.NotDeclared _ ->
                    throw new IllegalStateException("`" + declared + "` is asked for as a"
                            + " declaration of this compilation and resolves to none");
        };
    }

    /** What the check settled a value of {@code declared} holds, in the order it is laid out. */
    private Map<String, Type> fieldsOf(TypeSymbol.AtModule declared) {
        ValueShape shape = shapes.of(declared);
        if (shape == null) {
            throw new IllegalStateException("`" + declared + "` is a data this compile resolved and"
                    + " the check said nothing about what a value of it is made of");
        }
        Map<String, Type> out = new LinkedHashMap<>();
        for (ValueShape.Field field : shape.fields()) {
            out.put(field.name(), field.type());
        }
        return out;
    }
}
