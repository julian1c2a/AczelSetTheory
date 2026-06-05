import AczelSetTheory.CList.Basic

def main : IO Unit := do
  IO.println "Probando la canonización de un CList 'sucio'."
  let sucio := CList.mk (.cons CList.one (.cons CList.zero (.cons CList.one (.cons CList.zero (.cons CList.zero .nil)))))
  let limpio := CList.normalize sucio
  let esperado := CList.mk (.cons CList.zero (.cons CList.one .nil))
  IO.println s!"  Original: {repr sucio}"
  IO.println s!"Normalizado: {repr limpio}"
  IO.println s!"   Esperado: {repr esperado}"
  IO.println s!"¿Son iguales el normalizado y el esperado? {limpio == esperado}"
