// SVA checker for barrel_shifter. Bind this to the DUT and provide any convenient sampling clock/reset.
module barrel_shifter_sva #(
  parameter int W   = 8,
  parameter int SAW = 3
)(
  input  logic                  clk,
  input  logic                  rst_n,
  input  logic [W-1:0]          in,
  input  logic [SAW-1:0]        shift_amount,
  input  logic                  direction,   // 0=left, 1=right
  input  logic [W-1:0]          out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Basic functional equivalence
  a_equiv: assert property (out == (direction ? (in >> shift_amount) : (in << shift_amount)));

  // Shift amount within data width (guards parameter mismatches)
  a_amt_range: assert property (shift_amount <= W-1);

  // Zero-shift identity
  a_zero_shift: assert property (shift_amount == '0 |-> out == in);

  // Zero-fill checks at vacated bit positions
  a_zero_fill_L: assert property ((direction==1'b0 && shift_amount>0) |-> out[shift_amount-1:0] == '0);
  a_zero_fill_R: assert property ((direction==1'b1 && shift_amount>0) |-> out[W-1 -: shift_amount] == '0);

  // Bit preservation checks for the non-vacated ranges
  a_preserve_L: assert property (direction==1'b0 |-> out[W-1:shift_amount] == in[W-1-shift_amount:0]);
  a_preserve_R: assert property (direction==1'b1 |-> out[W-1-shift_amount:0] == in[W-1:shift_amount]);

  // Knownness: known inputs imply known output
  a_known: assert property (!$isunknown({in,shift_amount,direction}) |-> !$isunknown(out));

  // Combinational behavior: if inputs stable, output stable
  a_no_latch: assert property ($stable({in,shift_amount,direction}) |-> $stable(out));

  // Coverage: exercise both directions across all shift amounts
  genvar s;
  generate
    for (s = 0; s < (1<<SAW); s++) begin : gen_cov
      c_left_amt:  cover property (direction==1'b0 && shift_amount == s[SAW-1:0]);
      c_right_amt: cover property (direction==1'b1 && shift_amount == s[SAW-1:0]);
    end
  endgenerate

  // Coverage: interesting input patterns
  c_in_zero:   cover property (in == '0);
  c_in_ones:   cover property (&in);               // all ones
  c_in_onehot: cover property ($onehot(in));

endmodule

// Example bind (adjust clk/rst names to your TB):
// bind barrel_shifter barrel_shifter_sva #(.W(8), .SAW(3)) u_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));