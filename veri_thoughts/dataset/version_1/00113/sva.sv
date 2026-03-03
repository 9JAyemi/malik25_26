// SVA for decoder_3to8: active-low one-hot decode with explicit default on unknown in
// Bind example (hook up your sim clock/reset):
// bind decoder_3to8 decoder_3to8_sva u_dec_sva(.clk(clk), .rst_n(rst_n), .in(in), .out(out));

module decoder_3to8_sva
(
  input logic        clk,
  input logic        rst_n,
  input logic [2:0]  in,
  input logic [7:0]  out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Functional mapping: for known in, out == ~(1<<in)
  assert property (!$isunknown(in) |-> (out === ~(8'b0000_0001 << in)));

  // Output is fully known whenever input is known
  assert property (!$isunknown(in) |-> !$isunknown(out));

  // One-hot-low when input is known
  assert property (!$isunknown(in) |-> $onehot(~out));

  // Default behavior: if input contains X/Z, drive all 1s
  assert property ($isunknown(in) |-> (out === 8'hFF));

  // Coverage: each input value observed with correct output
  genvar i;
  for (i = 0; i < 8; i++) begin : C_IN
    cover property (!$isunknown(in) && (in == i[2:0]) && (out === ~(8'b0000_0001 << i)));
  end

  // Coverage: default path taken (unknown input -> all 1s)
  cover property ($isunknown(in) && (out === 8'hFF));

endmodule