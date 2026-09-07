Raw outputs of the packet floor certificate (2026-09-07).

  main.txt     packcert.py 4000 0.5 36 3.0 22   (X=4000, w=0.5, n=36, rho=3, J0=90)
  xcheck.txt   packcert.py 1000 0.4 28 2.8 22   (second quadrature, band [0,1000])
  assemble.txt packassemble.py main.txt 4000 90
  verify.txt   packverify.py main.txt xcheck.txt

Job logs: /home/chirurgie/.claude/jobs/4b35770d/tmp/h4_packet/{main,xcheck}.log
