import AczelSetTheory.CSets

def main : IO Unit := do
  IO.println "Probando la canonización de un CList 'sucio'."
  let sucio := CList.mk [CList.uno, CList.cero, CList.uno, CList.cero, CList.cero]
  let limpio := CList.normalizar sucio
  let esperado := CList.mk [CList.cero, CList.uno]
  IO.println s!"  Original: {repr sucio}"
  IO.println s!"Normalizado: {repr limpio}"
  IO.println s!"   Esperado: {repr esperado}"
  IO.println s!"¿Son iguales el normalizado y el esperado? {limpio == esperado}"
