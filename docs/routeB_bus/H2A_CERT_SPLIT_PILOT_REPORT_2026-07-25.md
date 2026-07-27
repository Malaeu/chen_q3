# H2a certificate split — binary64 pilot

Status: `CERT_PILOT_EXECUTED / CERT_EXACT_OPEN / NOT_RH`

## Split

- `cert.pilot`: binary64 diagnostic on the registered small grid.
- `cert.exact`: exact theorem leaf `ExactSectorOrdering`, still open.
- Exact consumer: Layer-B `PenaltyPilotFamily` / exact `PencilData`.

The pilot uses `G=I`, `K=Mfin_(m,N)=WeilMat_(m,N)`, the numerical
even-sector ground `q`,
`beta=(lambda_1+lambda_2)/2`, and `tau=lambda_2-lambda_1`.

## Results

| (m,N) | beta | tau | min_eig_cert | guard | result |
|---:|---:|---:|---:|---:|:---|
| (12,2) | 3.134257231822e-07 | 6.212990011959e-07 | 3.106495006050e-07 | 2.842e-14 | PSD |
| (12,3) | 7.238302693636e-10 | 1.443727144617e-09 | 7.218635782340e-10 | 2.842e-14 | PSD |
| (12,4) | 8.241133459871e-13 | 1.634065339246e-12 | 8.170435103387e-13 | 2.842e-14 | PSD |
| (13,2) | 3.882675357990e-07 | 7.705880340655e-07 | 3.852940170282e-07 | 2.842e-14 | PSD |
| (13,3) | 8.006070556314e-10 | 1.591905366404e-09 | 7.959526833735e-10 | 2.842e-14 | PSD |
| (13,4) | 1.974299883607e-12 | 3.929214363622e-12 | 1.964607203688e-12 | 2.842e-14 | PSD |
| (14,2) | 6.453572103894e-08 | 1.273363096605e-07 | 6.366815480439e-08 | 2.842e-14 | PSD |
| (14,3) | 2.434263853120e-10 | 4.842520353103e-10 | 2.421260211771e-10 | 2.842e-14 | PSD |
| (14,4) | 9.413030509140e-13 | 1.868819781338e-12 | 9.344086742672e-13 | 2.842e-14 | PSD |

Verdict: `PSD_ACHIEVABLE_ON_REGISTERED_SMALL_GRID`.

The `tau=0` planted control is negative beyond the binary64 guard
in every row.  The positive pilot margin is numerical evidence only.

## Exact queue leaf

```text
ExactSectorOrdering:
  epsilon_plus_1(m,N) < epsilon_minus_1(m,N)
  and
  epsilon_plus_1(m,N) < epsilon_plus_2(m,N)
```

Consumer:

```text
ExactSectorOrdering
  -> exact beta/tau penalty certificate
  -> ProjectApprox.PenaltyPilotFamily
  -> supply_H2a_Pstar_of_penaltyPilot
```

Stop: `H2A_EXACT_SECTOR_ORDERING_MISSING`.

No state file was modified; Bus 010 was not created.
