// SVA for comb_logic: Y = (A & B) | ~C, with internal structure checks and concise coverage

module comb_logic_sva (
  input A, B, C,
  input Y,
  input not_C,
  input and_AB
);
  // Immediate (deferred) functional and structural checks
  always_comb begin
    assert (#0 (not_C === ~C)) else
      $error("comb_logic SVA: not_C != ~C (A=%b B=%b C=%b not_C=%b)", A,B,C,not_C);

    assert (#0 (and_AB === (A & B))) else
      $error("comb_logic SVA: and_AB != (A & B) (A=%b B=%b C=%b and_AB=%b)", A,B,C,and_AB);

    assert (#0 (Y === (and_AB | not_C))) else
      $error("comb_logic SVA: Y != and_AB | not_C (and_AB=%b not_C=%b Y=%b)", and_AB,not_C,Y);

    assert (#0 (Y === ((A & B) | (~C)))) else
      $error("comb_logic SVA: Y != (A&B)|~C (A=%b B=%b C=%b Y=%b)", A,B,C,Y);

    if (!$isunknown({A,B,C})) begin
      assert (#0 !$isunknown(Y)) else
        $error("comb_logic SVA: Y is X/Z while inputs are known (A=%b B=%b C=%b Y=%b)", A,B,C,Y);
    end
  end

  // Functional coverage: all input combinations and each Y cause
  cover property (@(A or B or C) ({A,B,C} == 3'b000));
  cover property (@(A or B or C) ({A,B,C} == 3'b001));
  cover property (@(A or B or C) ({A,B,C} == 3'b010));
  cover property (@(A or B or C) ({A,B,C} == 3'b011));
  cover property (@(A or B or C) ({A,B,C} == 3'b100));
  cover property (@(A or B or C) ({A,B,C} == 3'b101));
  cover property (@(A or B or C) ({A,B,C} == 3'b110));
  cover property (@(A or B or C) ({A,B,C} == 3'b111));

  // Cause-specific coverage
  cover property (@(A or B or C) (C==0 && Y==1));               // ~C term drives Y
  cover property (@(A or B or C) (C==1 && A && B && Y==1));     // A&B term drives Y
  cover property (@(A or B or C) (C==1 && !(A&B) && Y==0));     // Y low case
endmodule

bind comb_logic comb_logic_sva sva_inst (.*);