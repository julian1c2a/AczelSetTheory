
path = 'AczelSetTheory/Axioms/Separation.lean'
with open(path, 'r', encoding='utf-8') as f:
    text = f.read()

text = text.replace('hP_resp xs xc h', 'hP_resp xc xs h')
text = text.replace('(Quotient.mk CList.Setoid xc ∈', '((Quotient.mk CList.Setoid xc : HFSet) ∈')
text = text.replace('Setoid a) P)', 'Setoid a : HFSet) P)')
text = text.replace('Setoid a) ↔', 'Setoid a : HFSet)) ↔')

with open(path, 'w', encoding='utf-8') as f:
    f.write(text)

