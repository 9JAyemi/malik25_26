// SVA for four_to_one. Bind this to the DUT.
// Focus: functional equivalence, X-propagation, supplies, stability, and coverage.
module four_to_one_sva ();
  // Trigger on any input edge
  default clocking cb @ (posedge A1 or negedge A1
                       or posedge A2 or negedge A2
                       or posedge B1 or negedge B1
                       or posedge B2 or negedge B2); endclocking
  // Disable checks when any relevant signal is X/Z
  default disable iff ($isunknown({A1,A2,B1,B2,VPWR,VGND}));

  // Golden function with explicit precedence to match DUT semantics
  let y_ref = ((A1 & (A2 == 1'b0)) & ((B1 == 1'b1) & (B2 == 1'b1)))
            | (((A1 == 1'b1) & (A2 == 1'b0)) & ((B1 == 1'b0) & (B2 == 1'b0)))
            | (((A1 == 1'b0) & (A2 == 1'b1)) & ((B1 == 1'b0) & (B2 == 1'b0)))
            | ((A1 & (A2 == 1'b1)) & ((B1 == 1'b0) & (B2 == 1'b0)));

  // Supplies must be correct
  ap_supplies_static: assert property (VPWR === 1'b1 && VGND === 1'b0);

  // No X/Z on output when inputs are known
  ap_no_x_on_y: assert property (!$isunknown({A1,A2,B1,B2}) |-> !$isunknown(Y));

  // Functional equivalence
  ap_func_eq: assert property (Y === y_ref);

  // Combinational stability: if inputs are stable, Y must be stable
  ap_no_spurious_y_change: assert property ($stable({A1,A2,B1,B2}) |-> $stable(Y));

  // Basic toggle coverage
  cp_y0: cover property (Y == 1'b0);
  cp_y1: cover property (Y == 1'b1);

  // Cover each product term that drives Y high (hit every ON-minterm)
  cp_term1: cover property ( (A1 & (A2 == 1'b0)) & ((B1 == 1'b1) & (B2 == 1'b1)) & (Y == 1'b1) );
  cp_term2: cover property ( ((A1 == 1'b1) & (A2 == 1'b0)) & ((B1 == 1'b0) & (B2 == 1'b0)) & (Y == 1'b1) );
  cp_term3: cover property ( ((A1 == 1'b0) & (A2 == 1'b1)) & ((B1 == 1'b0) & (B2 == 1'b0)) & (Y == 1'b1) );
  cp_term4: cover property ( (A1 & (A2 == 1'b1)) & ((B1 == 1'b0) & (B2 == 1'b0)) & (Y == 1'b1) );

  // Full input-space coverage (all 16 combinations)
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cg_all_inputs
      cp_all_inputs: cover property ({A1,A2,B1,B2} == i[3:0]);
    end
  endgenerate
endmodule

bind four_to_one four_to_one_sva sva_bind_inst();