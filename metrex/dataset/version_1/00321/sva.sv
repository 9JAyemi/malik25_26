// SVA for my_nand4
// Bind-in module; checks function, structure, X-prop; covers full input space.
module my_nand4_sva (input logic A, B, C, D, Y);

  // Sample on any edge of inputs/outputs/internals
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C or negedge C or
    posedge D or negedge D or
    posedge Y or negedge Y or
    posedge Y1 or negedge Y1 or
    posedge Y2 or negedge Y2 or
    posedge Y3 or negedge Y3
  ); endclocking

  // Functional equivalence (captures 4-state semantics, including X/Z)
  ap_func: assert property (Y === (A & B & C & D));

  // Structural consistency of the NAND/inverter chain
  ap_y1: assert property (Y1 === ~(A & B & C & D));
  ap_y2: assert property (Y2 === ~Y1);
  ap_y3: assert property (Y3 === ~Y2);
  ap_y4: assert property (Y  === ~Y3);

  // Dynamic implications on output transitions
  ap_rise: assert property ($rose(Y) |-> (A===1 && B===1 && C===1 && D===1));
  ap_fall: assert property ($fell(Y) |-> (A===0 || B===0 || C===0 || D===0));

  // X-propagation and dominance
  ap_any0:  assert property (((A===0)||(B===0)||(C===0)||(D===0)) |-> (Y===0));
  ap_all1:  assert property (((A===1)&&(B===1)&&(C===1)&&(D===1)) |-> (Y===1));
  ap_xprop: assert property ((!(A===0||B===0||C===0||D===0) && $isunknown({A,B,C,D})) |-> $isunknown(Y));

  // Coverage: all 16 input combinations, plus both output states
  genvar i;
  for (i=0; i<16; i++) begin : COV
    cp_in_vec: cover property ({A,B,C,D} === i[3:0]);
  end
  cp_y0: cover property (Y===0);
  cp_y1: cover property (Y===1);

endmodule

bind my_nand4 my_nand4_sva sva_inst(.*);