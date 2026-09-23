import Lean

open Lean

namespace VeriQuick.Instrumentation.Registry

private structure Entry where
  timed : Name
  valueTheorem : Name
  deriving Inhabited

private abbrev RegistryState := NameMap Entry

private def insert (state : RegistryState) (source : Name × Entry) : RegistryState :=
  state.insert source.1 source.2

private initialize extension : SimplePersistentEnvExtension (Name × Entry) RegistryState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := insert
    addImportedFn := fun entries => entries.foldl (fun state imported =>
      imported.foldl insert state) {}
  }

def timedForSource? (env : Environment) (source : Name) : Option Name :=
  (extension.getState env).find? source |>.map (·.timed)

/-- Find the pure source declaration registered for an instrumented declaration. -/
def sourceForTimed? (env : Environment) (timed : Name) : Option Name :=
  (extension.getState env).toList.findSome? fun (source, entry) =>
    if entry.timed == timed then some source else none

def valueTheorems (env : Environment) : Array Name :=
  (extension.getState env).toArray.map (fun (_, entry) => entry.valueTheorem)

def register (env : Environment) (source timed valueTheorem : Name) : Environment :=
  extension.addEntry env (source, { timed, valueTheorem })

end VeriQuick.Instrumentation.Registry
