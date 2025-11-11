// SVA for and_gate
module and_gate_sva (
    input logic A, B, Y,
    input logic VPWR, VGND
);
  // Sample on any relevant change; check after ##0 for settle
  event anychg;
  always @(A or B or Y or VPWR or VGND) -> anychg;
  default clocking @(anychg); endclocking

  // Functional correctness
  assert property (1'b1 |-> ##0 (Y === (A & B)));

  // Known inputs => known and correct output
  assert property (((!$isunknown(A)) && (!$isunknown(B))) |-> ##0 ((!$isunknown(Y)) && (Y === (A & B))));

  // Dominant-0 behavior
  assert property ((A===1'b0 || B===1'b0) |-> ##0 (Y===1'b0));

  // 1 & 1 => 1
  assert property ((A===1'b1 && B===1'b1) |-> ##0 (Y===1'b1));

  // X/Z propagation when no input is 0
  assert property ((( $isunknown(A) || $isunknown(B) ) && !(A===1'b0 || B===1'b0)) |-> ##0 $isunknown(Y));

  // Power rails must be correct
  assert property (1'b1 |-> (VPWR===1'b1 && VGND===1'b0));

  // Coverage: all input combos, output toggles, and 0-dominates-unknown
  cover property (##0 (A==1'b0 && B==1'b0 && Y==1'b0));
  cover property (##0 (A==1'b0 && B==1'b1 && Y==1'b0));
  cover property (##0 (A==1'b1 && B==1'b0 && Y==1'b0));
  cover property (##0 (A==1'b1 && B==1'b1 && Y==1'b1));
  cover property (##0 $rose(Y));
  cover property (##0 $fell(Y));
  cover property (##0 ((A===1'b0 && $isunknown(B) && Y===1'b0) ||
                       (B===1'b0 && $isunknown(A) && Y===1'b0)));
endmodule

bind and_gate and_gate_sva sva(.A(A), .B(B), .Y(Y), .VPWR(VPWR), .VGND(VGND));