package souther.compiler.codegen;

import souther.compiler.Reserved;
import souther.compiler.check.DeclarationReads;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.LinkageProjection;
import souther.compiler.jvm.LinkageRecord;
import souther.compiler.jvm.LinkageTarget;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.function.Function;

/**
 * Where one module's emission reads what the declarations it links against offer on the JVM, and
 * what records which of another module's declarations it read.
 *
 * <p>The two are one operation. A projection of another module's declaration is handed out by
 * {@link #behavior}, {@link #data} and {@link #value}, and handing one out is what records it: a
 * class that decided anything by what a declaration elsewhere offers was built against that
 * declaration, whether or not the decision left the declaration's name in the bytecode. A behavior
 * held as the unary {@code Behavior} is the case that shows why — the class names
 * {@code souther.runtime.Behavior} and never the behavior, and holds it that way because of how many
 * inputs the behavior takes.
 *
 * <p>The declarations are also read through the doors every reader below the check uses — a
 * declaration's node, what it says, which form it is, what it wraps. This is handed to those doors
 * ({@link DeclarationReads}), so a read through one of them records the declaration it was about.
 * And a class of another module named in the bytecode is recorded where its name is made
 * ({@link #named}).
 *
 * <p>A declaration of the module being emitted is answered and not recorded: a module is built
 * against its own declarations by being built.
 */
public final class LinkageReader implements DeclarationReads {

    private final String module;
    /** What this module provides, or null while that is what is being worked out. */
    private final Map<LinkageTarget, LinkageProjection> own;
    /** What another module's declaration offers, or null where nothing here provides it. */
    private final Function<LinkageTarget, LinkageProjection> elsewhere;
    private final SortedMap<LinkageTarget, LinkageProjection> read = new TreeMap<>();

    /**
     * A reader for working out what {@code module} provides, which reads other modules' declarations
     * and none of its own.
     *
     * @param elsewhere what another module's declaration offers, asked one declaration at a time so
     *                  a reader depends on the declarations it read and on no others
     */
    public LinkageReader(String module, Function<LinkageTarget, LinkageProjection> elsewhere) {
        this(module, null, elsewhere, Map.of());
    }

    /**
     * A reader for emitting {@code module}'s classes, starting from {@code alreadyRead}: what working
     * out its own projections read of other modules, which its classes are built against as much as
     * anything their code reads.
     */
    public LinkageReader(String module, Map<LinkageTarget, LinkageProjection> own,
                         Function<LinkageTarget, LinkageProjection> elsewhere,
                         Map<LinkageTarget, LinkageProjection> alreadyRead) {
        this.module = module;
        this.own = own == null ? null : Map.copyOf(own);
        this.elsewhere = elsewhere;
        this.read.putAll(alreadyRead);
    }

    /** What {@code behavior} offers, recorded where it is another module's. */
    public LinkageProjection.Behavior behavior(ValueName.Behavior behavior) {
        return (LinkageProjection.Behavior) projection(new LinkageTarget.Behavior(behavior));
    }

    /** What the declared type at {@code key} offers, recorded where it is another module's. */
    public LinkageProjection.Data data(TypeKey key) {
        return (LinkageProjection.Data) projection(new LinkageTarget.Data(key));
    }

    /** What the published value {@code value} offers, recorded where it is another module's. */
    public LinkageProjection.Value value(ValueName.Helper value) {
        return (LinkageProjection.Value) projection(new LinkageTarget.Value(value));
    }

    /**
     * A reader below the check was answered about {@code declaration}.
     *
     * <p>Recorded where it is a declaration another module of a compilation provides; what the
     * language declares is the same on every side of every artifact, and is not.
     */
    @Override
    public void read(TypeKey declaration) {
        if (!declaration.module().equals(module) && !Reserved.isNamespace(declaration.module())) {
            data(declaration);
        }
    }

    /**
     * The bytecode names {@code generated}. A class of another module's declaration is recorded as
     * that declaration.
     *
     * <p>Not every class there is has a declaration to record. A bridge case is one of its module's
     * result unions, and a value's entry is one of many on its module's class: both are recorded
     * where the behavior or the value they carry is read, which is before they are named.
     */
    void named(GeneratedClass generated) {
        switch (generated) {
            case GeneratedClass.Value v -> {
                if (v.type() instanceof TypeSymbol.AtModule at && !at.isDeclaredByLanguage()) {
                    read(at.key());
                }
            }
            case GeneratedClass.BehaviorInterface b -> behaviorNamed(b.module(), b.behavior());
            case GeneratedClass.BehaviorImpl b -> behaviorNamed(b.module(), b.behavior());
            case GeneratedClass.BehaviorResult b -> behaviorNamed(b.module(), b.behavior());
            case GeneratedClass.Encoder e -> named(e.of());
            case GeneratedClass.Decoder d -> named(d.of());
            case GeneratedClass.Ctfe c -> named(c.of());
            case GeneratedClass.Ensures e -> named(e.of());
            case GeneratedClass.ExampleFake f -> named(f.of());
            case GeneratedClass.BridgeCase _, GeneratedClass.Values _,
                 GeneratedClass.ModuleDeclarations _, GeneratedClass.Helpers _,
                 GeneratedClass.Lambda _ -> { }
        }
    }

    private void behaviorNamed(String declaredIn, String name) {
        if (!declaredIn.equals(module)) {
            behavior(new ValueName.Behavior(declaredIn, name));
        }
    }

    /** What was recorded: every declaration of another module this emission read, and what it read
     *  it as. */
    public SortedMap<LinkageTarget, LinkageProjection> read() {
        return new TreeMap<>(read);
    }

    /** What was recorded, as an artifact records it. */
    SortedMap<LinkageTarget, LinkageRecord> recordsRead() {
        return records(read);
    }

    /** What the module being emitted provides, as an artifact records it. */
    SortedMap<LinkageTarget, LinkageRecord> recordsProvided() {
        if (own == null) {
            throw new IllegalStateException("what " + module + " provides was not handed to its own"
                    + " emission");
        }
        return records(own);
    }

    private static SortedMap<LinkageTarget, LinkageRecord> records(
            Map<LinkageTarget, LinkageProjection> projections) {
        SortedMap<LinkageTarget, LinkageRecord> out = new TreeMap<>();
        projections.forEach((target, projection) -> out.put(target, LinkageRecord.of(projection)));
        return out;
    }

    private LinkageProjection projection(LinkageTarget target) {
        if (target.module().equals(module)) {
            if (own == null) {
                throw new IllegalStateException("what " + module + " provides is being worked out,"
                        + " and working it out read its own " + target.kind() + " "
                        + target.shown());
            }
            LinkageProjection found = own.get(target);
            if (found == null) {
                throw new IllegalStateException(module + " is emitted reading its own "
                        + target.kind() + " " + target.shown() + ", which it does not provide");
            }
            return found;
        }
        LinkageProjection found = elsewhere.apply(target);
        if (found == null) {
            throw new IllegalStateException(module + " is emitted reading the " + target.kind()
                    + " " + target.shown() + ", which nothing in this compilation provides");
        }
        read.put(target, found);
        return found;
    }
}
