/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import TypeChecker.Init.Prelude
import TypeChecker.Init.Notation
import TypeChecker.Init.Tactics
import TypeChecker.Init.TacticsExtra
import TypeChecker.Init.ByCases
import TypeChecker.Init.RCases
import TypeChecker.Init.Core
import TypeChecker.Init.Control
import TypeChecker.Init.Data.Basic
import TypeChecker.Init.WF
import TypeChecker.Init.WFTactics
import TypeChecker.Init.Data
import TypeChecker.Init.System
import TypeChecker.Init.Util
import TypeChecker.Init.Dynamic
import TypeChecker.Init.ShareCommon
import TypeChecker.Init.MetaTypes
import TypeChecker.Init.Meta
import TypeChecker.Init.NotationExtra
import TypeChecker.Init.SimpLemmas
import TypeChecker.Init.PropLemmas
import TypeChecker.Init.Hints
import TypeChecker.Init.Conv
import TypeChecker.Init.Guard
import TypeChecker.Init.Simproc
import TypeChecker.Init.SizeOfLemmas
import TypeChecker.Init.BinderPredicates
import TypeChecker.Init.Ext
import TypeChecker.Init.Omega
import TypeChecker.Init.MacroTrace
import TypeChecker.Init.Grind
