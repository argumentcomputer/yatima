import LSpec
import Yatima.Compiler.Compiler

open System LSpec

open Yatima.Compiler (CompileState compile)

structure TestGenerator where
  fixture : String
  extractors : List (CompileState → TestSeq)

def TestGenerator.gen (g : TestGenerator) : IO TestSeq := do
  return withExceptOk s!"Compiles {g.fixture}" (← compile g.fixture)
    fun stt => (g.extractors.map fun extr => extr stt).foldl (init := .done)
      (· ++ ·)
