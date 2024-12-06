inductive FmtStr
| question
| b | B | h | H | i | I | q | Q | e | f | d
--{'?', 'b', 'B', 'h', 'H', 'i', 'I', 'q', 'Q', 'e', 'f', 'd'}
namespace FmtStr
def toChar : FmtStr → Char
| question => '?'
| b => 'b' | B => 'B' | h => 'h' | H => 'H' | i => 'i' | I => 'I'
| q => 'q' | Q => 'Q' | e => 'e' | f => 'f' | d => 'd'

instance : Coe FmtStr Char := ⟨toChar⟩

class OfChar (c : Char) (α : Type) where
  ofChar : α

macro c:char : term =>
  match c.getChar with
  | '?' => `(question)
  | 'b' => `(b) | 'B' => `(B) | 'h' => `(h) | 'H' => `(H)
  | 'i' => `(i) | 'I' => `(I) | 'q' => `(q) | 'Q' => `(Q)
  | 'e' => `(e) | 'f' => `(f) | 'd' => `(d)
  | ch  => Lean.Macro.throwError s!"Unsupported character '{ch}' for FmtStr."
end FmtStr

#check ('?' : FmtStr)
inductive DType
| mk
  (priority: Int)  -- this determines when things get upcasted
  (itemsize: Nat)
  (name: String)
  (fmt: Option FmtStr)
  (count: Nat)
  (_scalar: Option DType)

#eval f!"2 + 2 {2 * 2}"
namespace DType
def name : DType → String
| mk _ _ name _ _ _ => name
def _scalar : DType → Option DType
| mk _ _ _ _ _ _scalar => _scalar
def new (priority:Int) (itemsize:Nat) (name:String) (fmt: Option FmtStr) : DType := mk priority itemsize name fmt 1 none
def void : DType := new (-1) 0 "void" none
def bool : DType := new 0 1 "bool" ('?' : FmtStr)
def int8 : DType := new 1 1 "signed char" ('b' : FmtStr)
def uint8 : DType := new 2 1 "unsigned char" ('B' : FmtStr)
def int16 : DType := new 3 2 "short" ('h' : FmtStr)
def uint16 : DType := new 4 2 "unsigned short" ('H' : FmtStr)
def int32 : DType := new 5 4 "int" ('i' : FmtStr)
def uint32 : DType := new 6 4 "unsigned int" ('I' : FmtStr)
def int64 : DType := new 7 8 "long" ('q' : FmtStr)
def uint64 : DType := new 8 8 "unsigned long" ('Q' : FmtStr)
def float16 : DType := new 9 2 "half" ('e' : FmtStr)
def bfloat16 : DType := new 10 2 "__bf16" none
def float32 : DType := new 11 4 "float" ('f' : FmtStr)
def float64 : DType := new 12 8 "double" ('d' : FmtStr)

end DType

def ConstType := Float ⊕ Int ⊕ Bool

instance : Coe Int ConstType :=
⟨fun x => Sum.inr <| Sum.inl x⟩

#check ((-1:Int) : ConstType)
