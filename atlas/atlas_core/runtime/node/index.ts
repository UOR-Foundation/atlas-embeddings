import ffi from 'ffi-napi';
import path from 'path';

const libPath = path.resolve(__dirname, '../../.lake/build/lib'); // adjust
const uor = ffi.Library(path.join(libPath, process.platform === 'win32' ? 'UOR.dll' : 'libUOR'), {
  'lean_initialize_uor': [ 'void', ['ulong'] ],
  'lean_uor_abi_version': [ 'uint', [] ],
  'lean_uor_pages': [ 'uint', [] ],
  'lean_uor_bytes': [ 'uint', [] ],
  'lean_uor_rclasses': [ 'uint', [] ],
  'lean_uor_r96_classify': [ 'uchar', ['uchar'] ],
  'lean_uor_phi_encode': [ 'uint', ['uchar', 'uchar'] ],
  'lean_uor_phi_page': [ 'uchar', ['uint'] ],
  'lean_uor_phi_byte': [ 'uchar', ['uint'] ],
  'lean_uor_truth_zero': [ 'uchar', ['uint'] ],
  'lean_uor_truth_add': [ 'uchar', ['uint', 'uint'] ],
});

uor.lean_initialize_uor(0);

export const AbiVersion = () => uor.lean_uor_abi_version();
export const Pages      = () => uor.lean_uor_pages();
export const Bytes      = () => uor.lean_uor_bytes();
export const RClasses   = () => uor.lean_uor_rclasses();

export const R96        = (b: number) => uor.lean_uor_r96_classify(b);
export const PhiEncode  = (p: number, b: number) => uor.lean_uor_phi_encode(p, b);
export const PhiPage    = (code: number) => uor.lean_uor_phi_page(code);
export const PhiByte    = (code: number) => uor.lean_uor_phi_byte(code);

export const TruthZero  = (budget: number) => uor.lean_uor_truth_zero(budget) === 1;
export const TruthAdd   = (a: number, b: number) => uor.lean_uor_truth_add(a, b) === 1;