// SVA for sky130_fd_sc_ls__o32ai
// Bind into DUT scope to access internals via (.*)
module sky130_fd_sc_ls__o32ai_sva (
  input logic A1, A2, A3, B1, B2,
  input logic Y,
  input logic nor0_out, nor1_out, or0_out_Y,
  input logic VPWR, VPB, VGND, VNB
);
  let GA = (A1 | A2 | A3);
  let GB = (B1 | B2);

  // Power rails must be as modeled
  assert property (@(VPWR or VPB or VGND or VNB)
                   (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0));

  // Gate-level composition matches internals
  assert property (@(A1 or A2 or A3) nor0_out  === ~(A1|A2|A3));
  assert property (@(B1 or B2)       nor1_out  === ~(B1|B2));
  assert property (@(nor0_out or nor1_out) or0_out_Y === (nor1_out | nor0_out));
  assert property (@(or0_out_Y or Y) Y === or0_out_Y);

  // Functional equivalence (4-state)
  assert property (@(A1 or A2 or A3 or B1 or B2 or Y)
                   Y === ~(GA & GB));

  // Deterministic corners
  assert property (@(A1 or A2 or A3 or B1 or B2 or Y)
                   (GA===1'b0 || GB===1'b0) |-> (Y===1'b1));
  assert property (@(A1 or A2 or A3 or B1 or B2 or Y)
                   (GA===1'b1 && GB===1'b1) |-> (Y===1'b0));

  // No X on Y when all inputs are known
  assert property (@(A1 or A2 or A3 or B1 or B2 or Y)
                   !$isunknown({A1,A2,A3,B1,B2}) |-> !$isunknown(Y));

  // X-propagation in critical cases
  assert property (@(A1 or A2 or A3 or B1 or B2 or Y)
                   (GA===1'b1 && $isunknown(GB)) |-> $isunknown(Y));
  assert property (@(A1 or A2 or A3 or B1 or B2 or Y)
                   (GB===1'b1 && $isunknown(GA)) |-> $isunknown(Y));

  // Functional coverage of key combos
  cover property (@(A1 or A2 or A3 or B1 or B2 or Y) (GA===1'b0 && GB===1'b0 && Y===1'b1));
  cover property (@(A1 or A2 or A3 or B1 or B2 or Y) (GA===1'b0 && GB===1'b1 && Y===1'b1));
  cover property (@(A1 or A2 or A3 or B1 or B2 or Y) (GA===1'b1 && GB===1'b0 && Y===1'b1));
  cover property (@(A1 or A2 or A3 or B1 or B2 or Y) (GA===1'b1 && GB===1'b1 && Y===1'b0));

  // Toggle coverage
  cover property (@(posedge A1) 1); cover property (@(negedge A1) 1);
  cover property (@(posedge A2) 1); cover property (@(negedge A2) 1);
  cover property (@(posedge A3) 1); cover property (@(negedge A3) 1);
  cover property (@(posedge B1) 1); cover property (@(negedge B1) 1);
  cover property (@(posedge B2) 1); cover property (@(negedge B2) 1);
  cover property (@(posedge Y) 1);  cover property (@(negedge Y) 1);
endmodule

bind sky130_fd_sc_ls__o32ai sky130_fd_sc_ls__o32ai_sva o32ai_sva_i (.*);