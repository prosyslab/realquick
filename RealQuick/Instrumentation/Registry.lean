import Lean

open Lean

namespace RealQuick.Instrumentation.Registry

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

def valueTheorems (env : Environment) : Array Name :=
  (extension.getState env).toArray.map (fun (_, entry) => entry.valueTheorem)

def register (env : Environment) (source timed valueTheorem : Name) : Environment :=
  extension.addEntry env (source, { timed, valueTheorem })

end RealQuick.Instrumentation.Registry
