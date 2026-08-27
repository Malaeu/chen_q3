---
TASK_ID: LINUX_SELF_CORRECTION_10
MODE: PAPER_AND_SOURCE_READ_ONLY
BODY: Linux-Claude
DATE: 2026-08-28
CORRECTS: ad621220, section 3 (the exact-equality claim)
ACCEPTS_VERDICT: 4049c26e
RH_CLAIM: false
---

# Correction 10 — the energy contract lives on the unprojected trial

## 1. Withdrawn

Report `ad621220` section 3 asserted the identity

    selectedPhysicalFourierEnergy = (4 pi^2/L^2) * ||N q||_2^2.

The formula is right and the object is wrong. `selectedPhysicalFourierEnergy`
(`D0PstarPhysicalFourierEnergyControl.lean:55`) is evaluated at `gTrial_m i h hLp`
— the **unprojected** trial. Our `q` is the coefficient row of
`kTrial_m_N = sTrial_m_N * P_m_N(gTrial_m)`, the **normalized finite projection**.
Two different vectors. C04.

## 2. What is correct

Two statements, and only these:

    physicalFourierEnergy( i, coefficients of kTrial_m_N ) = (4 pi^2/L^2) * ||N q||_2^2

is an exact finite identity, because on the projected object the coefficient
family is literally `q`. And for the full object,

    ||N q||_2 <= |sTrial_m_N| * (L/(2 pi)) * sqrt( physicalFourierEnergy(i, gTrial_m) ),

an inequality, because projection onto `|n| <= N` only drops non-negative terms
and the normalizer scales the row. The judge's repaired package is therefore

    SelectedPhysicalFourierEnergyControl + SelectedTrialNormalizerBounded
      =>  ||N q||_2 = O(L)  along the same selected family,

where the second contract does have a selected-Ferrers supplier,
`selectedTrialNormalizerBounded_of_selectedFerrersW5RateLedger`, Lean-proved
under frozen W5 inputs. The first remains an undischarged hypothesis, so the
package is not discharged.

## 3. Ledger

Fifteenth forbidden move: **check which vector a definition is applied to, not
only the shape of its formula.** The weight, the coefficient map and the sum
were all as I read them; the argument was a different trial. This is the same
error family as corrections 8 and 9 — matching a pattern instead of reading the
object — and it is now the third instance, so it is recorded as a habit rather
than an incident: before quoting a definition as a supplier, name its argument.
