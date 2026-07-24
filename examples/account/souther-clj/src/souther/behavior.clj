(ns souther.behavior
  "Implementing a Souther injected behavior from Clojure.

   A `required`/injected behavior is generated as an abstract base class (it carries the protected
   factories for its declared output cases, aimed at a Java subclass). Clojure implements it with
   `proxy`. Because a proxy cannot reach those protected factories, results are built through the
   public `decoder()` instead -- see `souther.decode/construct`. `defbehavior` is the small amount
   of sugar over `proxy` that names the implementation and mirrors the generated `apply` signature.
   `as-fn` turns a bound/unary behavior into a plain Clojure fn, called `(f input)` rather than
   `(.apply behavior input)`."
  (:import [clojure.lang Reflector]))

(defmacro defbehavior
  "Define `name` as a factory fn: its `deps` vector closes over the implementation's dependencies,
   and it returns a `proxy` of the abstract injected-behavior class `base` implementing the single
   method form `(apply [args...] body...)`. Build return values with `souther.decode/construct`.

     (defbehavior current-balance-impl [ds]
       CurrentBalance
       (apply [account] ... (construct Balance n) ...))"
  [name deps base method]
  `(defn ~name ~deps
     (proxy [~base] []
       ~method)))

(defn as-fn
  "Turn a unary Souther `Behavior` (the bound pipeline, or an injected behavior implementing
   `Behavior<I,O>`) into a Clojure function, so it is called `(f input)` instead of
   `(.apply behavior input)`."
  [behavior]
  (fn [input]
    (Reflector/invokeInstanceMethod behavior "apply" (object-array [input]))))
