// SVA for add_sub: concise, high-quality checks and coverage
// Bind into the DUT; provide a sampling clock from the TB.

`ifndef SYNTHESIS
module add_sub_sva #(
  parameter int W = 4
)(
  input  logic              clk,
  input  logic [W-1:0]      A,
  input  logic [W-1:0]      B,
  input  logic              SUBTRACT,
  input  logic [W-1:0]      SUM,
  input  logic              OVERFLOW
);

  default clocking cb @(posedge clk); endclocking

  // Golden math (1 extra bit for carry/borrow)
  logic [W:0] add_full, sub_full;
  assign add_full = {1'b0, A} + {1'b0, B};
  assign sub_full = {1'b0, A} - {1'b0, B};

  // Functional correctness
  a_add_sum:       assert property (!SUBTRACT |-> (SUM == add_full[W-1:0]));
  a_add_overflow:  assert property (!SUBTRACT |-> (OVERFLOW == add_full[W]));
  a_sub_sum:       assert property ( SUBTRACT |-> (SUM == sub_full[W-1:0]));
  a_sub_borrow:    assert property ( SUBTRACT |-> (OVERFLOW == (A < B)));

  // Combinational sanity: known-in => known-out; outputs stable when inputs stable
  a_known:         assert property (!$isunknown({A,B,SUBTRACT}) |-> !$isunknown({SUM,OVERFLOW}));
  a_stable:        assert property ($stable({A,B,SUBTRACT}) |-> $stable({SUM,OVERFLOW}));

  // Minimal, meaningful coverage
  c_add_no_ovf:    cover property (!SUBTRACT && (add_full[W] == 1'b0));
  c_add_ovf:       cover property (!SUBTRACT && (add_full[W] == 1'b1));
  c_sub_no_b:      cover property ( SUBTRACT && !(A < B));
  c_sub_b:         cover property ( SUBTRACT &&  (A < B));

  // Boundary corner cases
  c_add_boundary1: cover property (!SUBTRACT && (A==W'(4'hF)) && (B==W'(4'h1)));
  c_add_boundary0: cover property (!SUBTRACT && (A==W'(4'hF)) && (B==W'(4'h0)));
  c_sub_boundary0: cover property ( SUBTRACT && (A==W'(4'h0)) && (B==W'(4'h1)));
  c_sub_equal:     cover property ( SUBTRACT && (A==W'(4'hF)) && (B==W'(4'hF)));

endmodule

// Example bind (provide tb clock)
bind add_sub add_sub_sva #(.W(4)) add_sub_sva_i (
  .clk(tb_clk),
  .A(A), .B(B), .SUBTRACT(SUBTRACT),
  .SUM(SUM), .OVERFLOW(OVERFLOW)
);
`endif