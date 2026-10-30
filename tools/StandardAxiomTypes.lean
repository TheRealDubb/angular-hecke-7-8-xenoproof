import AngularPhysicalNormTwistNonvanishing

noncomputable section
set_option pp.universes true
#print propext
#print Classical.choice
#print Quot.sound
universe u
example : ∀ {a b : Prop}, (a ↔ b) → a = b := @propext
example : ∀ {α : Sort u}, Nonempty α → α := @Classical.choice
example : ∀ {α : Sort u} {r : α → α → Prop} {a b : α},
    r a b → Quot.mk r a = Quot.mk r b := @Quot.sound
