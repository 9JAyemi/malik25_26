// SVA checker for ASHIFTER_32bit
// Function implemented by DUT (based on its logic):
// - C==0: logical right shift by 1 -> S = {1'b0, D[31:1]}
// - C==1: left shift by 1 with MSB held -> S = {D[31], D[29:0], 1'b0}

module ASHIFTER_32bit_sva (
  input  logic        clk,     // sampling clock for concurrent SVA
  input  logic [31:0] D,
  input  logic        C,
  input  logic [31:0] S
);

  // Golden model
  function automatic logic [31:0] exp_val(logic [31:0] d, logic c);
    return c ? {d[31], d[29:0], 1'b0} : {1'b0, d[31:1]};
  endfunction

  // Immediate check (combinational, no clock dependence)
  always_comb begin
    if (!$isunknown({D,C})) begin
      assert (S == exp_val(D,C))
        else $error("ASHIFTER_32bit mismatch: C=%0b D=%h S=%h exp=%h", C, D, S, exp_val(D,C));
      assert (!$isunknown(S))
        else $error("ASHIFTER_32bit: X/Z on S with known inputs");
    end
  end

  // Concurrent SVA (optional, sampled on clk)
  default clocking cb @(posedge clk); endclocking

  // Functional equivalence by mode
  assert property ( !($isunknown({D,C})) && (C==1'b0) |-> S == {1'b0, D[31:1]} )
    else $error("Right-shift mode failed");
  assert property ( !($isunknown({D,C})) && (C==1'b1) |-> S == {D[31], D[29:0], 1'b0} )
    else $error("Left-hold-MSB mode failed");

  // Critical bit checks
  assert property ( !($isunknown({D,C})) && (C==1'b0) |-> (S[31]==1'b0 && S[0]==D[1]) )
    else $error("Right-shift edge bits failed");
  assert property ( !($isunknown({D,C})) && (C==1'b1) |-> (S[31]==D[31] && S[0]==1'b0) )
    else $error("Left-hold-MSB edge bits failed");

  // X-propagation guard
  assert property ( $isunknown({D,C}) || !$isunknown(S) )
    else $error("Unknowns propagated to S");

  // Coverage: exercise both modes and key corner patterns
  cover property ( C==1'b0 );                    // right-shift mode seen
  cover property ( C==1'b1 );                    // left-hold-MSB mode seen
  cover property ( C==1'b0 && D==32'h0000_0000 );
  cover property ( C==1'b1 && D==32'h0000_0000 );
  cover property ( C==1'b0 && D==32'hFFFF_FFFF );
  cover property ( C==1'b1 && D==32'hFFFF_FFFF );
  cover property ( C==1'b0 && D==32'h8000_0000 ); // sign bit only
  cover property ( C==1'b1 && D==32'h8000_0000 );
  cover property ( C==1'b0 ##1 C==1'b1 );        // mode toggle
  cover property ( C==1'b1 ##1 C==1'b0 );

endmodule

// Example bind (provide a clock from your TB, e.g., tb.sva_clk)
// bind ASHIFTER_32bit ASHIFTER_32bit_sva u_ashifter_32bit_sva(.clk(tb.sva_clk), .D(D), .C(C), .S(S));