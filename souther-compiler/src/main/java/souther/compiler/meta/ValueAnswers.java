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
import java.util.Set;
import java.util.function.Supplier;
import java.util.TreeMap;

/**
 * What a module says each value it publishes answers with, written so that another compilation can
 * read it without the module's source.
 *
 * <p>The type is the one the declaring module's own check settled the value as, and it is written as
 * the identities it is made of rather than as text a reader would have to resolve. A value's body
 * can name a type its module keeps to itself, so an answer spelled in the importer's names would
 * name nothing there; an identity says which declaration it is wherever it is read.
 *
 * <p>A name is written with its length in front of it and is read by counting, never by deciding
 * which characters may be in one. What a name may hold is the language's to say and is wider than
 * anything this format could list, so a format that lexed names would refuse a module the compiler
 * that wrote it accepted.
 *
 * <p>This is what the importer's executable representation of a value rests on: the type a call to
 * the value's entry is cast to. The published bodies are for the analyses and say nothing here.
 */
public final class ValueAnswers {

    private ValueAnswers() {
    }

    /**
     * What {@code settled} answers for each of {@code published}, the values {@code module} declares
     * for other modules to call, one line each in the order the names sort.
     *
     * <p>Only those. A module settles more definitions than it publishes — the ones written for its
     * rows and for its own entries among them — and what is recorded is what a reader can ask about.
     */
    static List<String> written(String module, Set<String> published,
                                Preserved.SettledValues settled) {
        Map<String, String> byName = new TreeMap<>();
        settled.signatures().forEach((value, signature) -> {
            if (value instanceof ValueName.Helper helper && helper.module().equals(module)
                    && published.contains(helper.name())) {
                String type = encode(signature.result());
                if (type == null) {
                    // What a check settled a published value as is a whole type. One that is still
                    // open is a check that did not finish, and a module that omitted it would read
                    // back as one whose value has no answer.
                    throw new IllegalStateException("`" + helper + "` is published and was settled"
                            + " as " + signature.result() + ", which is not a type a reader can be"
                            + " given");
                }
                byName.put(helper.name(), type);
            }
        });
        List<String> lines = new ArrayList<>();
        byName.forEach((name, type) -> lines.add(text(name) + "=" + type));
        return lines;
    }

    /**
     * The values {@code lines} record for {@code module}, as what each was settled as.
     *
     * <p>Null where a line is not one this reads, which is an artifact written by something else.
     */
    static Preserved.SettledValues read(String module, List<String> lines) {
        Map<ValueName, CompleteSignature> out = new LinkedHashMap<>();
        try {
            for (String line : lines) {
                Reader reader = new Reader(line);
                String name = reader.text();
                reader.expect('=');
                Type type = reader.type();
                reader.end();
                ValueName.Helper value = new ValueName.Helper(module, name);
                out.put(value, CompleteSignature.ofSettledValue(value, type));
            }
        } catch (Unreadable _) {
            return null;
        }
        return new Preserved.SettledValues(out);
    }

    /** {@code type} as text, or null where it is one no answer of a published value can be. */
    static String encode(Type type) {
        return switch (type) {
            case Type.Prim prim -> prim.shown();
            case Type.Nothing _ -> "Nothing";
            case Type.Never _ -> "Never";
            case Type.Ref ref -> "Ref(" + symbol(ref.name()) + ")";
            case Type.ListOf list -> around("List", List.of(list.element()));
            case Type.SetOf set -> around("Set", List.of(set.element()));
            case Type.OptionOf option -> around("Option", List.of(option.element()));
            case Type.MapOf map -> around("Map", List.of(map.key(), map.value()));
            case Type.TupleOf tuple -> around("Tuple", tuple.elements());
            case Type.FnOf fn -> {
                String params = around("Params", fn.params());
                String result = encode(fn.result());
                if (params == null || result == null) {
                    yield null;
                }
                yield "Fn(" + params + "," + result + ")";
            }
            case Type.Union union -> {
                List<String> members = new ArrayList<>();
                union.members().forEach(member -> members.add(symbol(member)));
                yield "Union(" + String.join(",", members) + ")";
            }
            // A type still open, or one that stands for a mistake, is not what a check settled a
            // value as.
            case Type.Var _, Type.MetaVar _, Type.Erroneous _ -> null;
        };
    }

    private static String around(String head, List<Type> types) {
        List<String> parts = new ArrayList<>();
        for (Type each : types) {
            String part = encode(each);
            if (part == null) {
                return null;
            }
            parts.add(part);
        }
        return head + "(" + String.join(",", parts) + ")";
    }

    private static String symbol(TypeSymbol symbol) {
        return switch (symbol) {
            case TypeSymbol.AtModule at -> "@" + text(at.module()) + "#" + text(at.name());
            case TypeSymbol.Primitive primitive -> "$" + primitive.primitive().shown();
            case TypeSymbol.LanguageCase language -> "!" + language.id().spelling();
        };
    }

    /** A name, counted: its length in characters, a colon, and the name itself. */
    private static String text(String name) {
        return name.length() + ":" + name;
    }

    /** The type {@code text} writes, or null where it writes none. */
    static Type decode(String text) {
        try {
            Reader reader = new Reader(text);
            Type type = reader.type();
            reader.end();
            return type;
        } catch (Unreadable _) {
            return null;
        }
    }

    /** Text that is not what this format writes. Never leaves this class. */
    private static final class Unreadable extends RuntimeException {
        private static final long serialVersionUID = 1L;

        Unreadable() {
            super(null, null, false, false);
        }
    }

    /** A cursor over the text. Anything it cannot read is {@link Unreadable}. */
    private static final class Reader {
        private final String text;
        private int at;

        Reader(String text) {
            this.text = text;
        }

        void end() {
            if (at != text.length()) {
                throw new Unreadable();
            }
        }

        void expect(char c) {
            if (at >= text.length() || text.charAt(at) != c) {
                throw new Unreadable();
            }
            at++;
        }

        private boolean eat(char c) {
            if (at < text.length() && text.charAt(at) == c) {
                at++;
                return true;
            }
            return false;
        }

        Type type() {
            String head = word();
            Type.Prim prim = Type.Prim.named(head);
            if (prim != null) {
                return prim;
            }
            return switch (head) {
                case "Nothing" -> new Type.Nothing();
                case "Never" -> new Type.Never();
                case "Ref" -> new Type.Ref(closed(this::symbol));
                case "List" -> new Type.ListOf(closed(this::type));
                case "Set" -> new Type.SetOf(closed(this::type));
                case "Option" -> new Type.OptionOf(closed(this::type));
                case "Map" -> {
                    expect('(');
                    Type key = type();
                    expect(',');
                    Type value = type();
                    expect(')');
                    yield new Type.MapOf(key, value);
                }
                case "Tuple" -> new Type.TupleOf(listed(this::type));
                case "Fn" -> {
                    expect('(');
                    if (!word().equals("Params")) {
                        throw new Unreadable();
                    }
                    expect('(');
                    List<Type> params = untilClosed(this::type);
                    expect(',');
                    Type result = type();
                    expect(')');
                    yield new Type.FnOf(params, result);
                }
                case "Union" -> {
                    SequencedSet<TypeSymbol> members = new LinkedHashSet<>(listed(this::symbol));
                    yield new Type.Union(members);
                }
                default -> throw new Unreadable();
            };
        }

        /** What is read between one pair of parentheses. */
        private <T> T closed(Supplier<T> read) {
            expect('(');
            T value = read.get();
            expect(')');
            return value;
        }

        /** Each of a comma-separated run between one pair of parentheses. */
        private <T> List<T> listed(Supplier<T> read) {
            expect('(');
            return untilClosed(read);
        }

        private <T> List<T> untilClosed(Supplier<T> read) {
            List<T> all = new ArrayList<>();
            if (eat(')')) {
                return all;
            }
            do {
                all.add(read.get());
            } while (eat(','));
            expect(')');
            return all;
        }

        private TypeSymbol symbol() {
            if (at >= text.length()) {
                throw new Unreadable();
            }
            char kind = text.charAt(at++);
            return switch (kind) {
                case '@' -> {
                    String module = text();
                    expect('#');
                    yield TypeSymbols.declared(new TypeKey(module, text()));
                }
                case '$' -> {
                    Type.Prim prim = Type.Prim.named(word());
                    if (prim == null) {
                        throw new Unreadable();
                    }
                    yield TypeSymbol.primitive(prim);
                }
                case '!' -> {
                    LanguageCaseId id = LanguageCaseId.named(word());
                    if (id == null) {
                        throw new Unreadable();
                    }
                    yield new TypeSymbol.LanguageCase(id);
                }
                default -> throw new Unreadable();
            };
        }

        /** A counted name: read by its length and by nothing about what it holds. */
        String text() {
            int from = at;
            while (at < text.length() && Character.isDigit(text.charAt(at))) {
                at++;
            }
            int length;
            try {
                length = Integer.parseInt(text.substring(from, at));
            } catch (NumberFormatException _) {
                throw new Unreadable();
            }
            expect(':');
            if (length <= 0 || at + length > text.length()) {
                throw new Unreadable();
            }
            String name = text.substring(at, at + length);
            at += length;
            return name;
        }

        /** One of this format's own words, which are ASCII by construction. */
        private String word() {
            int from = at;
            while (at < text.length() && Character.isLetter(text.charAt(at)) && text.charAt(at) < 128) {
                at++;
            }
            if (at == from) {
                throw new Unreadable();
            }
            return text.substring(from, at);
        }
    }
}
