package souther.compiler.sites;

import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
import souther.compiler.Reserved;
import souther.compiler.check.Symbols;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.query.Answer;
import souther.compiler.query.Db;
import souther.compiler.query.Names;
import souther.compiler.query.Sites;

import java.util.Optional;

/**
 * What is known about one revision of one module's source, as an editor asks it.
 *
 * <p>The boundary, and the only thing outside the compiler reads. Everything it answers is about an
 * occurrence the source wrote, found by the characters it was written over, and every answer comes
 * from this one revision — nothing here is carried over from a revision that compiled earlier, so an
 * answer is either about what the buffer says now or is absent.
 *
 * <p>Built where it is used and dropped there. It holds a way to reach answers rather than a set of
 * them, which is what {@link Names#derivedSymbols} is and for the same reason: it has no equality to
 * be memoised by, and a caller that kept one would be keeping the compilation it was made from.
 *
 * <p>Absent where the occurrences of the module could not be told apart. What an editor does then is
 * everything it can do from the syntax alone — where a bracket's match is, what the declarations in
 * a file are — and nothing that rests on knowing which occurrence a position is. Half of a snapshot
 * is not published.
 */
public final class SemanticSnapshot {

    private final AuthoredSites sites;
    private final Symbols symbols;

    private SemanticSnapshot(AuthoredSites sites, Symbols symbols) {
        this.sites = sites;
        this.symbols = symbols;
    }

    /**
     * What {@code db} can be asked about {@code module}, or empty where it cannot be asked.
     *
     * <p>Empty rather than partial. A module whose source does not resolve has no settled reading of
     * its names, and one whose occurrences collide has no way to say which occurrence a position is;
     * neither is a snapshot with less in it.
     */
    public static Optional<SemanticSnapshot> of(Db db, String module) {
        Answer<AuthoredSites> occurrences = db.ask(new Sites.Authored(module));
        Answer<Symbols> scope = Names.derivedSymbols(db, module);
        return occurrences.present() && scope.present()
                ? Optional.of(new SemanticSnapshot(occurrences.value(), scope.value()))
                : Optional.empty();
    }

    /**
     * What the left of the {@code .} is, for the narrowest thing written over {@code cursor}.
     *
     * <p>Empty where no access was written there. That a receiver is a value whose type nothing here
     * states is a different answer and is {@link MemberReceiver.UntypedValue} — a reader that offers
     * nothing for both still knows which of them it was told.
     */
    public Optional<MemberReceiver> memberReceiverAround(SourcePos cursor) {
        return memberReceiverOf(sites.innermostContaining(cursor));
    }

    /**
     * The same, for a caller that has the access's extent rather than a place inside it.
     *
     * <p>Two entry points and not one method that guesses which it was handed. What an editor has is
     * a cursor; what a reader that already walked the tree has is an extent, and an extent that is
     * an occurrence is one occurrence while a place is inside several.
     */
    public Optional<MemberReceiver> memberReceiverOf(Region extent) {
        return switch (sites.written(extent)) {
            // A field taken off a value. That it is one is already settled: the parser reads
            // `m.name` and `x.field` alike, and this is a field read because a binding was in force
            // where the chain is rooted.
            case Hir.FieldAccess access ->
                    Optional.of(new MemberReceiver.UntypedValue(access.target().region()));
            case Hir.Var written -> namespaceOf(written.written());
            case null, default -> Optional.empty();
        };
    }

    /**
     * The namespace a qualified name is reached through, or empty where the name is not qualified or
     * its qualifier names none.
     *
     * <p>Answered to the module rather than to the spelling. An import may bring a module in under
     * any name it likes, so what {@code m} is is a question about this module's imports, and a
     * reader handed the spelling would have to ask it again.
     */
    private Optional<MemberReceiver> namespaceOf(WrittenName name) {
        String written = name.canonical();
        int lastDot = written.lastIndexOf('.');
        if (lastDot < 0 || name.segments().size() < 2) {
            return Optional.empty();
        }
        String qualifier = written.substring(0, lastDot);
        // Every segment but the last, which is what the qualifier is written over. Taken from the
        // occurrences the name carries rather than measured in the spelling: the two differ by
        // whatever the grammar lets stand between a qualifier and the name it qualifies.
        Region at = new Region(name.segments().getFirst().start(),
                name.segments().get(name.segments().size() - 2).end());
        String module = symbols.scope().moduleOfQualifier(qualifier);
        if (module != null) {
            return Optional.of(new MemberReceiver.Namespace.OfModule(module, at));
        }
        return Reserved.isQualifier(qualifier)
                ? Optional.of(new MemberReceiver.Namespace.OfLibrary(qualifier, at))
                : Optional.empty();
    }
}
