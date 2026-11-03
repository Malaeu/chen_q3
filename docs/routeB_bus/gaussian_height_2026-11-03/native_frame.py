from pathlib import Path
import ctypes,subprocess,numpy as np
P=Path(__file__).resolve().parent
def load():
 lib=P/'frame.so'
 if not lib.exists()or lib.stat().st_mtime<(P/'frame.c').stat().st_mtime:
  subprocess.run(['gcc','-O3','-shared','-fPIC',str(P/'frame.c'),'-o',str(lib),'-l:libmpfr.so.6','-lgmp'],check=True)
 dll=ctypes.CDLL(str(lib));fn=dll.frame_mgs;fn.argtypes=[ctypes.c_int,ctypes.c_int,ctypes.c_long,ctypes.POINTER(ctypes.c_char_p),ctypes.POINTER(ctypes.c_double),ctypes.POINTER(ctypes.c_double)];fn.restype=ctypes.c_int;return fn
_fn=None
def frame(rows,bits):
 global _fn
 if _fn is None:_fn=load()
 nr=len(rows);nc=len(rows[0]);raw=[str(x).encode()for row in rows for x in row];data=(ctypes.c_char_p*len(raw))(*raw);out=np.empty((nr,nc));ratios=np.empty(nr)
 status=_fn(nr,nc,bits,data,out.ctypes.data_as(ctypes.POINTER(ctypes.c_double)),ratios.ctypes.data_as(ctypes.POINTER(ctypes.c_double)))
 if status:raise ArithmeticError('MPFR MGS failure '+str(status))
 return out,ratios

def ldl_counts(A,shifts,bits=400):
 lib=P/'frame.so'
 if not lib.exists()or lib.stat().st_mtime<(P/'frame.c').stat().st_mtime:load()
 dll=ctypes.CDLL(str(lib));fn=dll.shifted_ldl;fn.argtypes=[ctypes.c_int,ctypes.c_long,ctypes.POINTER(ctypes.c_char_p),ctypes.c_int,ctypes.POINTER(ctypes.c_char_p),ctypes.POINTER(ctypes.c_int)];fn.restype=ctypes.c_int
 n=len(A);raw=[str(x).encode()for row in A for x in row];data=(ctypes.c_char_p*len(raw))(*raw);s=[str(x).encode()for x in shifts];ss=(ctypes.c_char_p*len(s))(*s);counts=(ctypes.c_int*len(s))()
 status=fn(n,bits,data,len(s),ss,counts)
 if status:raise ArithmeticError('native LDL failure '+str(status))
 return list(counts)
