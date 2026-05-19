import LeanTre2Ta.Basic.TimedWord

namespace LeanTre2Ta

inductive TRE (α : Type u) where
  | empty : TRE α
  | epsilon : TRE α
  | atom : α → TRE α
  | union : TRE α → TRE α → TRE α
  | inter : TRE α → TRE α → TRE α
  | concat : TRE α → TRE α → TRE α
  | star : TRE α → TRE α
  | plus : TRE α → TRE α
  | within : TRE α → Interval → TRE α

end LeanTre2Ta
