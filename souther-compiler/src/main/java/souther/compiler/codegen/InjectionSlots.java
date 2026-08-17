package souther.compiler.codegen;

import souther.compiler.types.ValueName;

import java.lang.constant.ClassDesc;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The fields one generated class holds its injected behaviors in.
 *
 * <p>A field is the class's own, not the behavior's. What a behavior is called belongs to the module
 * that declares it, and two modules may call one thing the same — so a class named after what it
 * holds has one field where it wants two, which the JVM reads as a class file with a member written
 * twice. The name here is the position instead, which no two dependencies of one construction share.
 *
 * <p>The position, and not something drawn from the dependency: a class holding {@code app.a.f} and
 * {@code app.b.f} would still have to spell them apart, and any spelling built from the declaration
 * is a name a reader downstream will try to read the declaration back out of.
 *
 * <p>Held as one value per class rather than worked out where each field is written, so the class
 * that declares the field, the constructor that fills it and every read of it cannot disagree. A
 * dependency the class does not hold has no field, and asking for one is refused rather than
 * answered with a name nothing declared.
 */
final class InjectionSlots {

    /** One dependency, the field this class keeps it in, and the JVM type of that field. */
    record Slot(ValueName.Behavior dependency, String fieldName, ClassDesc type) {}

    private static final InjectionSlots NONE = new InjectionSlots(List.of(), Map.of());

    private final List<Slot> slots;
    private final Map<ValueName.Behavior, Slot> byDependency;

    private InjectionSlots(List<Slot> slots, Map<ValueName.Behavior, Slot> byDependency) {
        this.slots = slots;
        this.byDependency = byDependency;
    }

    /**
     * The slots of a class holding {@code held}, in that order — which is the injecting
     * constructor's parameter order and the order an example passes its fakes in.
     */
    static InjectionSlots of(List<ValueName.Behavior> held, CodegenContext ctx) {
        if (held.isEmpty()) {
            return NONE;
        }
        List<Slot> slots = new ArrayList<>();
        Map<ValueName.Behavior, Slot> byDependency = new LinkedHashMap<>();
        for (int i = 0; i < held.size(); i++) {
            ValueName.Behavior dependency = held.get(i);
            Slot slot = new Slot(dependency, "$dep" + i, ctx.requiredFieldType(dependency));
            slots.add(slot);
            // A dependency two stages of one composition share is one field, and the first position
            // it appeared at is the one they both read (spec §composition-with-requirements).
            byDependency.putIfAbsent(dependency, slot);
        }
        return new InjectionSlots(List.copyOf(slots), Map.copyOf(byDependency));
    }

    /** A class holding nothing injected. */
    static InjectionSlots none() {
        return NONE;
    }

    List<Slot> all() {
        return slots;
    }

    boolean isEmpty() {
        return slots.isEmpty();
    }

    /**
     * The field this class keeps {@code dependency} in.
     *
     * <p>Refused where the class holds no field for it: a read of a field nothing declared is a
     * {@code NoSuchFieldError} at load time, and the walk that asked for it had already decided
     * this construction needs the dependency. Which is this compiler disagreeing with itself.
     */
    Slot of(ValueName.Behavior dependency) {
        Slot slot = byDependency.get(dependency);
        if (slot == null) {
            throw new IllegalStateException("nothing was injected for `" + dependency
                    + "`, so this class holds no field to read it from; it holds " + byDependency.keySet());
        }
        return slot;
    }
}
