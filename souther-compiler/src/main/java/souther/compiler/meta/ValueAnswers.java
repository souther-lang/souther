package souther.compiler.meta;

import souther.compiler.check.Preserved;
import souther.compiler.core.CompleteSignature;
import souther.compiler.types.LanguageCaseId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.SequencedSet;

/**
 * What a module says each value it publishes answers with, written so that another compilation can
 * read it without the module's source.
 *
 * <p>The type is the one the declaring module's own check settled the value as, and it is written as
 * the identities it is made of rather than as text a reader would have to resolve. A value's body
 * can name a type its module keeps to itself, so an answer spelled in the importer's names would
 * name nothing there; an identity says which declaration it is wherever it is read.
 *
 * <p>This is what the importer's executable representation of a value rests on: the type a call to
 * the value's entry is cast to. The published bodies are for the analyses and say nothing here.
 */
public final class ValueAnswers {

    private ValueAnswers() {
    }

    /**
     * {@code settled}'s answers for the values {@code module} declares, one {@code name=type} line
     * each, in the order the names sort.
     */
    static List<String> written(String module, Preserved.SettledValues settled) {
        Map<String, String> byName = new java.util.TreeMap<>();
        settled.signatures().forEach((value, signature) -> {
            if (value instanceof ValueName.Helper helper && helper.module().equals(module)) {
                String type = encode(signature.result());
                if (type != null) {
                    byName.put(helper.name(), type);
                }
            }
        });
        List<String> lines = new ArrayList<>();
        byName.forEach((name, type) -> lines.add(name + "=" + type));
        return lines;
    }

    /**
     * The values {@code lines} record for {@code module}, as what each was settled as.
     *
     * <p>Null where a line is not one this reads, which is an artifact written by something else.
     */
    static Preserved.SettledValues read(String module, List<String> lines) {
        Map<ValueName, CompleteSignature> out = new LinkedHashMap<>();
        for (String line : lines) {
            int at = line.indexOf('=');
            if (at <= 0) {
                return null;
            }
            Type type = decode(line.substring(at + 1));
            if (type == null) {
                return null;
            }
            ValueName.Helper value = new ValueName.Helper(module, line.substring(0, at));
            out.put(value, CompleteSignature.ofSettledValue(value, type));
        }
        return new Preserved.SettledValues(out);
    }

    /** {@code type} as text, or null where it is one no answer of a published value can be. */
    static String encode(Type type) {
        return switch (type) {
            case Type.Prim prim -> prim.shown();
            case Type.Nothing _ -> "Nothing";
            case Type.Never _ -> "Never";
            case Type.Ref ref -> wrap("Ref", symbol(ref.name()));
            case Type.ListOf list -> wrap("List", encode(list.element()));
            case Type.SetOf set -> wrap("Set", encode(set.element()));
            case Type.OptionOf option -> wrap("Option", encode(option.element()));
            case Type.MapOf map -> wrap("Map", encode(map.key()), encode(map.value()));
            case Type.TupleOf tuple -> wrap("Tuple", each(tuple.elements()));
            case Type.FnOf fn -> wrap("Fn", wrap("Params", each(fn.params())), encode(fn.result()));
            case Type.Union union -> {
                List<String> members = new ArrayList<>();
                union.members().forEach(member -> members.add(symbol(member)));
                yield wrap("Union", String.join(",", members));
            }
            // A type still open, or one that stands for a mistake, is not what a check settled a
            // value as.
            case Type.Var _, Type.MetaVar _, Type.Erroneous _ -> null;
        };
    }

    private static String each(List<Type> types) {
        List<String> parts = new ArrayList<>();
        for (Type each : types) {
            String part = encode(each);
            if (part == null) {
                return null;
            }
            parts.add(part);
        }
        return String.join(",", parts);
    }

    private static String wrap(String head, String... parts) {
        List<String> all = new ArrayList<>();
        for (String part : parts) {
            if (part == null) {
                return null;
            }
            all.add(part);
        }
        return head + "(" + String.join(",", all) + ")";
    }

    private static String symbol(TypeSymbol symbol) {
        return switch (symbol) {
            case TypeSymbol.AtModule at -> "@" + at.module() + "#" + at.name();
            case TypeSymbol.Primitive primitive -> "$" + primitive.primitive().shown();
            case TypeSymbol.LanguageCase language -> "!" + language.id().spelling();
        };
    }

    /** The type {@code text} writes, or null where it writes none. */
    static Type decode(String text) {
        Reader reader = new Reader(text);
        Type type = reader.type();
        return type != null && reader.atEnd() ? type : null;
    }

    /** A cursor over the text, which fails by answering null all the way out. */
    private static final class Reader {
        private final String text;
        private int at;

        Reader(String text) {
            this.text = text;
        }

        boolean atEnd() {
            return at == text.length();
        }

        Type type() {
            String head = word();
            if (head.isEmpty()) {
                return null;
            }
            Type.Prim prim = Type.Prim.named(head);
            if (prim != null) {
                return prim;
            }
            return switch (head) {
                case "Nothing" -> new Type.Nothing();
                case "Never" -> new Type.Never();
                case "Ref" -> {
                    TypeSymbol symbol = opened() ? symbolThenClose() : null;
                    yield symbol == null ? null : new Type.Ref(symbol);
                }
                case "List" -> {
                    Type element = opened() ? single() : null;
                    yield element == null ? null : new Type.ListOf(element);
                }
                case "Set" -> {
                    Type element = opened() ? single() : null;
                    yield element == null ? null : new Type.SetOf(element);
                }
                case "Option" -> {
                    Type element = opened() ? single() : null;
                    yield element == null ? null : new Type.OptionOf(element);
                }
                case "Map" -> {
                    if (!opened()) {
                        yield null;
                    }
                    Type key = type();
                    Type value = key != null && eat(',') ? type() : null;
                    yield value != null && eat(')') ? new Type.MapOf(key, value) : null;
                }
                case "Tuple" -> {
                    List<Type> elements = opened() ? listThenClose() : null;
                    yield elements == null ? null : new Type.TupleOf(elements);
                }
                case "Fn" -> {
                    if (!opened() || !word().equals("Params") || !opened()) {
                        yield null;
                    }
                    List<Type> params = listThenClose();
                    Type result = params != null && eat(',') ? type() : null;
                    yield result != null && eat(')') ? new Type.FnOf(params, result) : null;
                }
                case "Union" -> {
                    SequencedSet<TypeSymbol> members = opened() ? membersThenClose() : null;
                    yield members == null ? null : new Type.Union(members);
                }
                default -> null;
            };
        }

        private Type single() {
            Type type = type();
            return type != null && eat(')') ? type : null;
        }

        private List<Type> listThenClose() {
            List<Type> types = new ArrayList<>();
            if (eat(')')) {
                return types;
            }
            do {
                Type next = type();
                if (next == null) {
                    return null;
                }
                types.add(next);
            } while (eat(','));
            return eat(')') ? types : null;
        }

        private SequencedSet<TypeSymbol> membersThenClose() {
            SequencedSet<TypeSymbol> members = new LinkedHashSet<>();
            do {
                TypeSymbol next = symbol();
                if (next == null) {
                    return null;
                }
                members.add(next);
            } while (eat(','));
            return eat(')') ? members : null;
        }

        private TypeSymbol symbolThenClose() {
            TypeSymbol symbol = symbol();
            return symbol != null && eat(')') ? symbol : null;
        }

        private TypeSymbol symbol() {
            if (at >= text.length()) {
                return null;
            }
            char kind = text.charAt(at++);
            String body = word();
            switch (kind) {
                case '@' -> {
                    if (!eat('#')) {
                        return null;
                    }
                    String name = word();
                    return body.isEmpty() || name.isEmpty()
                            ? null : TypeSymbols.declared(new TypeKey(body, name));
                }
                case '$' -> {
                    Type.Prim prim = Type.Prim.named(body);
                    return prim == null ? null : TypeSymbol.primitive(prim);
                }
                case '!' -> {
                    LanguageCaseId id = LanguageCaseId.named(body);
                    return id == null ? null : new TypeSymbol.LanguageCase(id);
                }
                default -> {
                    return null;
                }
            }
        }

        private boolean opened() {
            return eat('(');
        }

        private boolean eat(char c) {
            if (at < text.length() && text.charAt(at) == c) {
                at++;
                return true;
            }
            return false;
        }

        private String word() {
            int from = at;
            while (at < text.length()
                    && (Character.isLetterOrDigit(text.charAt(at)) || text.charAt(at) == '_'
                    || text.charAt(at) == '.')) {
                at++;
            }
            return text.substring(from, at);
        }
    }
}
