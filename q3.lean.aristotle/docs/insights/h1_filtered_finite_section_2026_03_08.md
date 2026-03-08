# H1 Filtered Finite Section (2026-03-08)

## Claim

The preferred first-pass Suzuki bridge object is not the raw finite Q3 block
`Q_M = T_M[P_A] - T_P^{(M)}`, but the filtered section

`\widetilde Q_M = \Delta_+^* Q_{M+1} \Delta_+`,

where `\Delta_+ = I + L` is the coefficient-side shift filter corresponding to
multiplication by `1+z`.

## Volterra Data

Keep the filtered Volterra realization

- `J_a = (I_0^{(a)})^* I_0^{(a)}`
- `I_0^{(a)} S_{a,M} = U_a M_{1+z}|_{P_M}`

Then the pullback metric is explicit:

`B_M = S_{a,M}^* J_a S_{a,M} = T_M[|1+z|^2] = \Delta_+^* \Delta_+`.

## Why This Is Better

The previous coarse transfer only used `0 <= B_M <= 4I`, so a bulk bound
`Q_M >= c(a) I` yielded only `Q_M >= (c(a)/4) B_M`.

The filtered section removes that loss:

if `Q_{M+1} >= c(a) I`, then

`\widetilde Q_M = \Delta_+^* Q_{M+1} \Delta_+ >= c(a) \Delta_+^* \Delta_+ = c(a) B_M`.

So the filtered Q3 gap transfers to `J_a`-coercivity with no loss of constant.

## New H1 Target

The preferred first-pass pair-intertwining target becomes

`S_{a,M}^* G_g[a] S_{a,M} = \kappa(a) \widetilde Q_M + F_{a,M}`,

where `F_{a,M}` is zero or an explicit finite-rank Suzuki cap.

## Next Brick

The next honest step is exact entrywise comparison between the Suzuki tail
matrix on the filtered basis and the filtered finite Q3 section
`\widetilde Q_M`, separating bulk from the genuine finite-rank cap.
