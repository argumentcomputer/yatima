namespace Grin

inductive Tag where
-- Suspended full applications
| F : Tag
-- Partial applications
| P : Tag
-- Saturated constructors
| C : Tag

inductive Binding where

inductive Program where
| bindings : Binding → List Binding → Program

end Grin
