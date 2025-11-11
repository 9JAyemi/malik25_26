// SVA for barrel_shifter
// Assumes a sample clock and active-low reset are provided from the environment.
// Bind example (provide your own clk,rst_n):
//   bind barrel_shifter barrel_shifter_sva u_barrel_shifter_sva (.*,.clk(tb_clk),.rst_n(tb_rst_n));

module barrel_shifter_sva
(
  input  logic         clk,
  input  logic         rst_n,
  input  logic [31:0]  data_in,
  input  logic [4:0]   shift_amount,
  input  logic [31:0]  data_out,
  input  logic         zero_flag
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  function automatic logic [31:0] rol32(logic [31:0] x, logic [4:0] n);
    return (x << n) | (x >> (32 - n));
  endfunction

  // Functional correctness: rotate-left by shift_amount
  property p_rotate_left;
    data_out == rol32(data_in, shift_amount);
  endproperty
  assert property (p_rotate_left)
    else $error("barrel_shifter: data_out != rol32(data_in, shift_amount)");

  // Zero flag correctness
  assert property (zero_flag == (data_out == 32'h0))
    else $error("barrel_shifter: zero_flag mismatch");

  // Knownness: known inputs imply known outputs
  assert property ((!$isunknown({data_in, shift_amount})) |-> !$isunknown({data_out, zero_flag}))
    else $error("barrel_shifter: X/Z propagation detected");

  // Bit-count preserved by rotation
  assert property ($countones(data_out) == $countones(data_in))
    else $error("barrel_shifter: population count not preserved");

  // Special cases
  assert property ((shift_amount == 5'd0) |-> (data_out == data_in))
    else $error("barrel_shifter: shift_amount==0 must pass-through");

  assert property ((data_in == 32'h0000_0000) |-> (data_out == 32'h0000_0000 && zero_flag))
    else $error("barrel_shifter: all-zero input behavior incorrect");

  assert property ((data_in == 32'hFFFF_FFFF) |-> (data_out == 32'hFFFF_FFFF && !zero_flag))
    else $error("barrel_shifter: all-one input behavior incorrect");

  assert property ($onehot0(data_in) |-> $onehot0(data_out))
    else $error("barrel_shifter: onehot preservation failed");

  // Coverage: hit all shift amounts, both zero_flag states, and some data patterns
  genvar i;
  generate
    for (i = 0; i < 32; i++) begin : gen_cover_shift_vals
      cover property (shift_amount == i);
    end
  endgenerate

  cover property (zero_flag == 1'b0);
  cover property (zero_flag == 1'b1);

  cover property (data_in == 32'h0000_0000);
  cover property (data_in == 32'hFFFF_FFFF);
  cover property ($onehot(data_in));

  // Sanity cover: observable rotation for a single-hot input across a few shifts
  cover property ($onehot(data_in) && (shift_amount == 5'd1) && data_out == rol32(data_in, 5'd1));
  cover property ($onehot(data_in) && (shift_amount == 5'd8) && data_out == rol32(data_in, 5'd8));
  cover property ($onehot(data_in) && (shift_amount == 5'd31) && data_out == rol32(data_in, 5'd31));

endmodule