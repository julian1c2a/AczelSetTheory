import AczelSetTheory.CSets

def main : IO Unit := do
  IO.println "Probando la canonización de un CList 'sucio'."
  let sucio := CList.mk [CList.one, CList.zero, CList.one, CList.zero, CList.zero]
  let limpio := CList.normalize sucio
  let esperado := CList.mk [CList.zero, CList.one]
  IO.println s!"  Original: {repr sucio}"
  IO.println s!"Normalizado: {repr limpio}"
  IO.println s!"   Esperado: {repr esperado}"
  IO.println s!"¿Son iguales el normalizado y el esperado? {limpio == esperado}"
