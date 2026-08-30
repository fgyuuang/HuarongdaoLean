# Continuous-class cardinality certificate

## Result

The compiled proof exports:

```lean
Huarongdao.ClassicFullSpace.continuousClass_card_eq_898_complete
```

Its proposition is:

```lean
@Fintype.card ContinuousClass
  (ComponentRun.Lawful.continuousClassFintypeOfLawful
    Huarongdao.ClassicFullSpace.fullSpaceRun_lawful) = 898
```

The same module also exports the proof-facing DFS certificate:

```lean
Huarongdao.ClassicFullSpace.fullSpaceRun_lawful
```

## Certificate layers

The expensive finite checks are isolated in two modules:

1. `Huarongdao/ClassicFullSpaceFiniteCertificate.lean`
   checks all validity, labels, roots, parent edges, and closed-successor
   obligations for `fullSpaceRun`.
2. `Huarongdao/ClassicFullSpaceRootCountCertificate.lean`
   checks `fullSpaceRun.roots.size = 898`.

`Huarongdao/ClassicContinuousClassCardCore.lean` combines those certificates
with generator completeness and indexed-state injectivity.  The public wrapper
is `Huarongdao/ClassicContinuousClassCardFinal.lean`.

## Reuse

The compiled artifacts are stored under:

```text
.lake/build/lib/lean/Huarongdao/
```

In particular:

```text
ClassicFullSpaceFiniteCertificate.olean
ClassicFullSpaceRootCountCertificate.olean
ClassicContinuousClassCardCore.olean
ClassicContinuousClassCardFinal.olean
```

Downstream files should import:

```lean
import Huarongdao.ClassicContinuousClassCardFinal
```

and use `continuousClass_card_eq_898_complete`.  Importing the final module
only loads the saved proof objects; it does not run `native_decide` again.

## Trust boundary

The finite facts are proved with Lean's `native_decide` reflection mechanism.
The resulting `.olean` files are proof artifacts checked by Lean when loaded.
No project-specific `axiom` or `sorry` is introduced by these modules.
