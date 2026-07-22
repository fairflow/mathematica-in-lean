/-
Driving creative telescoping THROUGH THE BRIDGE.

`examples/CreativeTelescoping.lean` deliberately uses **no** bridge code: there, the
certificate was found in a separate Mathematica session and I hand-wrote the Lean.
This file closes that gap for the *discovery* step — it `import`s the bridge and calls
the kernel, so Mathematica finds the certificate and Lean fetches it at elaboration
time.

`WZCert[F, n, k]` (defined on the Wolfram side, `wolfram/lean_form.wl`, which the
bridge kernel loads) runs creative telescoping by ansatz: given only the summand it
returns `{a0(n), a1(n), R(n,k)}` — the recurrence `a0·F(n,k) + a1·F(n+1,k) =
G(n,k+1) − G(n,k)` with `G = R·F`.  What comes back below is exactly the certificate
that `CreativeTelescoping.lean`'s `sum_choose_sq` verifies soundly.

Run (needs a live kernel):
  MATHEMATICA_BRIDGE_LEANFORM="$(pwd)/wolfram/lean_form.wl" \
    lake env lean examples/ZeilbergerBridge.lean

What is and isn't automated: the **discovery** is now bridge-driven (the kernel finds
the certificate, fetched here at elaboration). The **proof** — building `cert_step`,
telescoping, induction — is still hand-written in `CreativeTelescoping.lean`; turning
the fetched certificate into a machine-generated Lean proof is a future
`mathematica_telescope` tactic (it would parse `R`, define `Gc`, discharge `cert_step`
by `field_simp; ring`, telescope, and induct).
-/
import Mathematica

-- ∑_{k} C(n,k):  finder ⇒ recurrence {a0,a1} = {-2, 1}, i.e. S(n+1) = 2·S(n),
-- with certificate R = -k/(n+1-k).  (This is L0b, now discovered via the bridge.)
#mathematica "WZCert[Function[{nn, kk}, Binomial[nn, kk]], n, k]"

-- ∑_{k} C(n,k)²:  finder ⇒ recurrence {-(4n+2), n+1}, i.e. (n+1)S(n+1) = (4n+2)S(n),
-- and certificate R = k²(2k - 3n - 3)/(n+1-k)².
-- That R is *exactly* the `Rc`/`Gc` hand-coded and verified in CreativeTelescoping.lean:
-- the bridge auto-finds the certificate the sound Lean proof checks.
#mathematica "WZCert[Function[{nn, kk}, Binomial[nn, kk]^2], n, k]"
