// SVA for nand4bb
module nand4bb_sva (
  input logic A_N, B_N, C, D,
  input logic Y,
  input logic VPWR, VGND, VPB, VNB
);

  // Sample on any input edge (combinational changes)
  event comb_ev = (posedge A_N or negedge A_N
                 or posedge B_N or negedge B_N
                 or posedge C   or negedge C
                 or posedge D   or negedge D);
  default clocking cb @ (comb_ev); endclocking

  // Functional equivalence
  assert property (Y === ~(A_N & B_N & C & D));

  // Output 0 iff all inputs are 1
  assert property ((Y === 1'b0) |-> ({A_N, B_N, C, D} === 4'b1111));

  // Any 0 input forces Y = 1 (even with X/Z on others)
  assert property (((A_N === 1'b0) || (B_N === 1'b0) || (C === 1'b0) || (D === 1'b0)) |-> (Y === 1'b1));

  // All inputs known -> output known
  assert property ((!$isunknown({A_N, B_N, C, D})) |-> (!$isunknown(Y)));

  // X-propagation: one input X with others 1 -> Y is X
  assert property ( ($isunknown(A_N) && {B_N, C, D} === 3'b111) |-> $isunknown(Y) );
  assert property ( ($isunknown(B_N) && {A_N, C, D} === 3'b111) |-> $isunknown(Y) );
  assert property ( ($isunknown(C  ) && {A_N, B_N, D} === 3'b111) |-> $isunknown(Y) );
  assert property ( ($isunknown(D  ) && {A_N, B_N, C} === 3'b111) |-> $isunknown(Y) );

  // Power/ground pins sanity
  assert property (VPWR === 1'b1 && VPB === 1'b1 && VGND === 1'b0 && VNB === 1'b0);

  // Input space coverage (all 16 combinations)
  genvar gi;
  generate
    for (gi = 0; gi < 16; gi++) begin : COV_IN
      cover property ({A_N, B_N, C, D} == gi[3:0]);
    end
  endgenerate

  // Output value and transitions coverage
  cover property (Y === 1'b0);
  cover property (Y === 1'b1);
  cover property ($past(Y,1) === 1'b0 && Y === 1'b1);
  cover property ($past(Y,1) === 1'b1 && Y === 1'b0);

  // Optional: observe any X on Y (for X-prop scenarios)
  cover property ($isunknown(Y));

endmodule

// Bind into DUT
bind nand4bb nand4bb_sva u_nand4bb_sva (.*);