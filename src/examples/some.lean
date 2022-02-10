import data.nat.basic

open classical


lemma all_zero : ∃ a b c : ℕ, a + b + c = 0 :=
begin
  use 0,
  use 0,
  use 0,
end

example : 1 = 1 :=
begin
  choose a b c h using all_zero,
  exact rfl,
end