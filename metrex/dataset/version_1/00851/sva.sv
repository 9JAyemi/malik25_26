// SVA for barrel_shifter. Bind this module in your env and connect clk/rst_n.
module barrel_shifter_sva #(
  parameter int W = 8,
  parameter int S = 8
)(
  input  logic               clk,
  input  logic               rst_n,
  input  logic [W-1:0]       in,
  input  logic [1:0]         shift_dir,  // 0: right (arith), non-0: left (logical)
  input  logic [$clog2(W):0] shift_amt,  // 3 bits for W=8
  input  logic [W-1:0]       out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Golden expected behavior (per comments): right = arithmetic, left = logical zero-fill
  function automatic logic [W-1:0] exp_out (logic [W-1:0] i,
                                            logic [1:0]   d,
                                            logic [$clog2(W):0] a);
    logic [W-1:0] r;
    if (a > S)        r = '0;
    else if (a == 0)  r = i;
    else if (d == 0)  r = $signed(i) >>> a;
    else              r = i << a;
    return r;
  endfunction

  // Functional equivalence
  assert property (out == exp_out(in, shift_dir, shift_amt))
    else $error("barrel_shifter: out mismatch: dir=%0b amt=%0d in=%0h out=%0h exp=%0h",
                shift_dir, shift_amt, in, out, exp_out(in, shift_dir, shift_amt));

  // No-shift passthrough
  assert property (shift_amt == 0 |-> out == in);

  // Left shift: zero-fill and bit mapping (for 1..W-1)
  assert property ((shift_dir != 0) && (shift_amt inside {[1:W-1]})
                   |-> (out[shift_amt-1:0] == '0)
                       && (out[W-1:shift_amt] == in[W-1-shift_amt:0]));

  // Right shift: arithmetic fill and bit mapping (for 1..W-1)
  assert property ((shift_dir == 0) && (shift_amt inside {[1:W-1]})
                   |-> (out[W-1:W-shift_amt] == {shift_amt{in[W-1]}})
                       && (out[W-1-shift_amt:0] == in[W-1:shift_amt]));

  // If amt > S, DUT promises zero
  assert property (shift_amt > S |-> out == '0);

  // Determinism and 2-state behavior
  assert property ($stable({in,shift_dir,shift_amt}) |-> $stable(out));
  assert property (!$isunknown({in,shift_dir,shift_amt}) |-> !$isunknown(out));

  // Coverage: directions x all shift amounts, incl. edge cases
  genvar k;
  generate
    for (k = 0; k < W; k++) begin : COVS
      cover property (shift_dir == 0 && shift_amt == k);
      cover property (shift_dir != 0 && shift_amt == k);
    end
  endgenerate
  // Cover arithmetic-right with negative input and large shifts
  cover property (shift_dir == 0 && in[W-1] && shift_amt inside {[1:W-1]});
  // Cover left shifts that drop MSBs
  cover property ((shift_dir != 0) && (shift_amt inside {[1:W-1]}) && (|in[W-1:W-shift_amt]));
  // Unreachable path in given RTL (amt > S) — include for completeness
  cover property (shift_amt > S);

endmodule

// Example bind (connect clk/rst_n from your env):
// bind barrel_shifter barrel_shifter_sva #(.W(8), .S(8)) u_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));