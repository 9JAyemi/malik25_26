// SVA checker for mag_comp
// - Clocked (bind to a sim clock). Guards against Xs. Concise but complete.
// - Verifies exact function, mutual exclusivity/one-hot, no spurious asserts,
//   and stability when inputs are stable. Includes basic functional coverage.

module mag_comp_sva #(
  parameter bit USE_RST = 0
)(
  input  logic       clk,
  input  logic       rst_n,    // if USE_RST==0, ignored
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       EQ,
  input  logic       GT,
  input  logic       LT
);

  default clocking cb @(posedge clk); endclocking

  // Helper predicates
  function automatic bit known_in();  return !$isunknown({A,B});           endfunction
  function automatic bit known_out(); return !$isunknown({EQ,GT,LT});      endfunction
  function automatic bit in_reset();  return (USE_RST && !rst_n);          endfunction

  // 1) Outputs shall never be X/Z when inputs are known
  assert property (disable iff (in_reset())
                   known_in() |-> known_out())
    else $error("mag_comp: outputs unknown while inputs known");

  // 2) Exact functionality (forward direction)
  assert property (disable iff (in_reset())
                   known_in() && (A == B) |-> (EQ && !GT && !LT))
    else $error("mag_comp: EQ case violated");
  assert property (disable iff (in_reset())
                   known_in() && (A >  B) |-> (GT && !EQ && !LT))
    else $error("mag_comp: GT case violated");
  assert property (disable iff (in_reset())
                   known_in() && (A <  B) |-> (LT && !EQ && !GT))
    else $error("mag_comp: LT case violated");

  // 3) No spurious assertions (reverse direction)
  assert property (disable iff (in_reset())
                   known_out() && EQ |-> (A == B))
    else $error("mag_comp: EQ asserted when A!=B");
  assert property (disable iff (in_reset())
                   known_out() && GT |-> (A >  B))
    else $error("mag_comp: GT asserted when A<=B");
  assert property (disable iff (in_reset())
                   known_out() && LT |-> (A <  B))
    else $error("mag_comp: LT asserted when A>=B");

  // 4) Mutual exclusivity and completeness (one-hot)
  assert property (disable iff (in_reset())
                   known_out() |-> $onehot({EQ,GT,LT}))
    else $error("mag_comp: outputs not one-hot");

  // 5) Combinational stability: if inputs hold, outputs hold
  assert property (disable iff (in_reset())
                   $stable({A,B}) |-> $stable({EQ,GT,LT}))
    else $error("mag_comp: outputs changed while inputs stable");

  // Coverage: hit all relational regions and key corners
  cover property (known_in() && (A == B) && EQ);
  cover property (known_in() && (A >  B) && GT);
  cover property (known_in() && (A <  B) && LT);

  // Corner cases
  cover property (known_in() && (A==4'h0) && (B==4'h0) && EQ);
  cover property (known_in() && (A==4'hF) && (B==4'h0) && GT);
  cover property (known_in() && (A==4'h0) && (B==4'hF) && LT);

endmodule

// Example bind (adjust clk/rst_n to your environment):
// bind mag_comp mag_comp_sva #(.USE_RST(0)) u_mag_comp_sva (.*,.clk(tb_clk), .rst_n(1'b1));