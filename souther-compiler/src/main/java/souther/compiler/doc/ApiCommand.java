package souther.compiler.doc;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.types.Type;

import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * {@code souther api}: the standard library's published surface, one name per line with the
 * signature the checker resolved. The listing answers "what is there and how is it called"; the
 * {@code --source} form prints a module's own {@code .sou} text, whose comments say why each
 * declaration is shaped the way it is.
 */
public final class ApiCommand {

    private ApiCommand() {}

    public static int run(String[] args, PrintStream out, PrintStream err) {
        if (args.length == 0) {
            listPublished(out, null);
            return 0;
        }
        if (args[0].equals("--source")) {
            if (args.length < 2) {
                err.println("usage: souther api --source <Module>");
                return 2;
            }
            return printSource(args[1], out, err);
        }
        if (args[0].equals("--search")) {
            if (args.length < 2 || args[1].isBlank()) {
                err.println("`--search` needs a term to look for");
                err.println("usage: souther api --search <term>");
                return 2;
            }
            String needle = args[1].toLowerCase();
            List<String> found = surface().entrySet().stream()
                    .filter(e -> e.getKey().toLowerCase().contains(needle))
                    .map(e -> line(e.getKey(), e.getValue()))
                    .toList();
            if (found.isEmpty()) {
                err.println("no stdlib name contains `" + args[1] + "`");
                return 0;
            }
            found.forEach(out::println);
            return 0;
        }
        String asked = args[0];
        if (asked.contains(".")) {
            Signature signature = surface().get(asked);
            if (signature == null) {
                err.println("no stdlib declaration `" + asked + "`");
                return 2;
            }
            out.println(line(asked, signature));
            // A signature says what to pass, not what it means — whether a span counts both ends,
            // whether a division aborts or answers a case. That is in the module's own source.
            err.println("`souther api --source " + asked.substring(0, asked.indexOf('.'))
                    + "` for what it means");
            return 0;
        }
        if (!Prelude.isQualifier(asked)) {
            err.println("no stdlib module `" + asked + "`");
            err.println("modules: " + String.join(", ", Prelude.qualifiers().stream().sorted().toList()));
            return 2;
        }
        listPublished(out, asked + ".");
        return 0;
    }

    /** One callable name's parameters, as written, and the type its call answers with. */
    private record Signature(List<String> paramNames, List<Type> paramTypes, Type result) {}

    private static void listPublished(PrintStream out, String prefix) {
        surface().forEach((name, signature) -> {
            if (prefix == null || name.startsWith(prefix)) {
                out.println(line(name, signature));
            }
        });
    }

    /**
     * Every name a call may be written with, in module order.
     *
     * <p>This is the callable surface, not the declared one: a name written as sugar over a private
     * helper — {@code List.fold}, which the checker rewrites to {@code List.foldFrom(…, 0)} — is
     * what the specification tells a reader to call, so it is listed under its own name and with
     * only the arguments its caller writes. Leaving it out would have this command contradict the
     * specification about what exists.
     */
    private static Map<String, Signature> surface() {
        Map<String, Signature> surface = new LinkedHashMap<>();
        for (Map.Entry<String, Prelude.PreludeEntry> e : Prelude.entries().entrySet()) {
            if (Prelude.published().contains(e.getKey())) {
                surface.put(e.getKey(), declared(e.getValue(), e.getValue().signature().params().size()));
            }
        }
        for (Map.Entry<String, Prelude.Rewrite> e : Prelude.rewrites().entrySet()) {
            Prelude.PreludeEntry target = Prelude.entry(e.getValue().target().qualified());
            if (target != null) {
                surface.put(e.getKey(), declared(target, e.getValue().keptArgs()));
            }
        }
        return surface;
    }

    private static Signature declared(Prelude.PreludeEntry entry, int arity) {
        List<Ast.FnParam> params = entry.declaration().params();
        List<Type> types = entry.signature().params();
        List<String> names = new ArrayList<>();
        List<Type> kept = new ArrayList<>();
        for (int i = 0; i < arity && i < params.size(); i++) {
            names.add(params.get(i).binder().name());
            kept.add(types.get(i));
        }
        return new Signature(names, kept, entry.signature().result());
    }

    private static String line(String qualifiedName, Signature signature) {
        StringBuilder sb = new StringBuilder(qualifiedName).append("(");
        for (int i = 0; i < signature.paramNames().size(); i++) {
            if (i > 0) {
                sb.append(", ");
            }
            sb.append(signature.paramNames().get(i)).append(": ")
                    .append(Type.show(signature.paramTypes().get(i)));
        }
        sb.append(")");
        if (signature.result() != null) {
            sb.append(" : ").append(Type.show(signature.result()));
        }
        return sb.toString();
    }

    private static int printSource(String alias, PrintStream out, PrintStream err) {
        if (!Prelude.isQualifier(alias)) {
            err.println("no stdlib module `" + alias + "`");
            err.println("modules: " + String.join(", ", Prelude.qualifiers().stream().sorted().toList()));
            return 2;
        }
        String resource = "/souther/" + alias.toLowerCase() + ".sou";
        try (InputStream in = ApiCommand.class.getResourceAsStream(resource)) {
            if (in == null) {
                err.println("no bundled source for `" + alias + "`");
                return 2;
            }
            out.print(new String(in.readAllBytes(), StandardCharsets.UTF_8));
            return 0;
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
