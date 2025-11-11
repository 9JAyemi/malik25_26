// SVA for manchester_coder
`ifndef MANCHESTER_CODER_SVA
`define MANCHESTER_CODER_SVA

module manchester_coder_sva (
  input logic clk_in,
  input logic data_in,
  input logic data_out,
  input logic data_decoded
);

  // Default clock for sequential checks
  default clocking cb @ (posedge clk_in); endclocking

  // Combinational relation: data_out is XNOR of clk_in and data_in
  a_comb_xnor: assert property (
    @(posedge clk_in or negedge clk_in or posedge data_in or negedge data_in)
      data_out === (clk_in ~^ data_in)
  );

  // If inputs are known, output must be known (no X/Z leakage)
  a_no_x_leak_out: assert property (
    @(posedge clk_in or negedge clk_in or posedge data_in or negedge data_in)
      (!$isunknown({clk_in, data_in})) |-> !$isunknown(data_out)
  );

  // Sequential decode: on each posedge, if data_out was known then next posedge data_decoded matches it
  a_decode_updates: assert property (
    !$isunknown(data_out) |=> (data_decoded === $past(data_out))
  );

  // If data_out was unknown at a posedge, data_decoded must hold its previous value
  a_decode_holds_on_x: assert property (
    $isunknown(data_out) |=> (data_decoded === $past(data_decoded))
  );

  // data_decoded only changes on posedge clk_in (no glitches on data_in or negedge clk)
  a_no_glitch_decoded: assert property (
    @(negedge clk_in or posedge data_in or negedge data_in) $stable(data_decoded)
  );

  // Basic functional coverage
  c_out_is_0:     cover property (@(posedge clk_in) (data_out === 1'b0));
  c_out_is_1:     cover property (@(posedge clk_in) (data_out === 1'b1));
  c_dec_0_to_1:   cover property (@(posedge clk_in) ($past(data_out)===1'b0) |=> (data_decoded===1'b0) ##1 (data_decoded===1'b1));
  c_dec_1_to_0:   cover property (@(posedge clk_in) ($past(data_out)===1'b1) |=> (data_decoded===1'b1) ##1 (data_decoded===1'b0));
  c_out_unknown:  cover property (@(posedge clk_in) $isunknown(data_out));

endmodule

// Bind into DUT
bind manchester_coder manchester_coder_sva sva (
  .clk_in      (clk_in),
  .data_in     (data_in),
  .data_out    (data_out),
  .data_decoded(data_decoded)
);

`endif