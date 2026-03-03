// SVA for karnaugh_map: F must equal B ^ C ^ D; independent of A
module karnaugh_map_sva (
  input logic A, B, C, D,
  input logic F
);

  // Functional equivalence: sample after combinational update (##0), ignore X/Z on inputs
  property p_func_eq;
    @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
      !$isunknown({A,B,C,D}) |-> ##0 (F === (B ^ C ^ D));
  endproperty
  assert property (p_func_eq) else $error("F != B^C^D");

  // A must not affect F when B,C,D stable
  property p_A_independent;
    @(posedge A or negedge A)
      !$isunknown({A,B,C,D}) && $stable({B,C,D}) |-> ##0 $stable(F);
  endproperty
  assert property (p_A_independent) else $error("F changed on A-only toggle");

  // Single-bit toggle behavior on B,C,D causes F to toggle (with others stable)
  property p_B_flip;
    @(posedge B or negedge B)
      !$isunknown({A,B,C,D}) && $stable({C,D}) |-> ##0 $changed(F);
  endproperty
  assert property (p_B_flip) else $error("F did not toggle on B-only edge");

  property p_C_flip;
    @(posedge C or negedge C)
      !$isunknown({A,B,C,D}) && $stable({B,D}) |-> ##0 $changed(F);
  endproperty
  assert property (p_C_flip) else $error("F did not toggle on C-only edge");

  property p_D_flip;
    @(posedge D or negedge D)
      !$isunknown({A,B,C,D}) && $stable({B,C}) |-> ##0 $changed(F);
  endproperty
  assert property (p_D_flip) else $error("F did not toggle on D-only edge");

  // X-propagation guard: with clean inputs, F must be known
  property p_no_x_out;
    @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
      !$isunknown({A,B,C,D}) |-> ##0 !$isunknown(F);
  endproperty
  assert property (p_no_x_out) else $error("F is X/Z with known inputs");

  // Coverage: hit both F polarities and key toggle scenarios
  cover property (@(posedge F) 1);
  cover property (@(negedge F) 1);
  cover property (@(posedge A or negedge A) $stable({B,C,D}) ##0 $stable(F));
  cover property (@(posedge B or negedge B) $stable({C,D}) ##0 $changed(F));
  cover property (@(posedge C or negedge C) $stable({B,D}) ##0 $changed(F));
  cover property (@(posedge D or negedge D) $stable({B,C}) ##0 $changed(F));

  // Full minterm coverage (all 16 input combinations with correct F)
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : COV_ALL_INPUTS
      cover property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
          {A,B,C,D} == i[3:0] ##0 (F === (i[2]^i[1]^i[0]))
      );
    end
  endgenerate

endmodule

// Bind to DUT
bind karnaugh_map karnaugh_map_sva sva_kmap (.A(A), .B(B), .C(C), .D(D), .F(F));