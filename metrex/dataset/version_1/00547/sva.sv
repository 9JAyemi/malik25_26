// SVA checker for sky130_fd_sc_hvl__o22ai
// Binds to every instance and verifies function, internals, X-prop, and covers key cases.

module o22ai_sva;
  // Trigger on any edge of any input (combinational sampling)
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge B1 or negedge B1 or
    posedge B2 or negedge B2
  ); endclocking

  // Short-hands
  wire a_or = A1 | A2;
  wire b_or = B1 | B2;

  // Functional correctness (only when inputs are known)
  assert property ( !$isunknown({A1,A2,B1,B2})
                    |-> (Y === ~((A1|A2) & (B1|B2))) );

  // Output must be known when inputs are known
  assert property ( !$isunknown({A1,A2,B1,B2}) |-> !$isunknown(Y) );

  // Gate-level internal consistency (guard against Xs)
  assert property ( !$isunknown({B1,B2}) |-> (nor0_out   === ~(B1|B2)) );
  assert property ( !$isunknown({A1,A2}) |-> (nor1_out   === ~(A1|A2)) );
  assert property ( !$isunknown({nor0_out,nor1_out})
                    |-> (or0_out_Y === (nor0_out | nor1_out)) );
  assert property ( !$isunknown(or0_out_Y) |-> (Y === or0_out_Y) );

  // Functional corner-case covers (truth-table partitions)
  cover property ( !$isunknown({A1,A2,B1,B2}) && (a_or==0) && (b_or==0) && (Y==1) );
  cover property ( !$isunknown({A1,A2,B1,B2}) && (a_or==0) && (b_or==1) && (Y==1) );
  cover property ( !$isunknown({A1,A2,B1,B2}) && (a_or==1) && (b_or==0) && (Y==1) );
  cover property ( !$isunknown({A1,A2,B1,B2}) && (a_or==1) && (b_or==1) && (Y==0) );

  // Toggle coverage on Y
  cover property ( $rose(Y) );
  cover property ( $fell(Y) );
endmodule

bind sky130_fd_sc_hvl__o22ai o22ai_sva o22ai_sva_i();