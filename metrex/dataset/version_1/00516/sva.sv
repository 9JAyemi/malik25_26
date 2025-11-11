// SVA for top_module and its decoder. Bind these into the DUT.
// Concise, high-signal-coverage checks + key functional covers.

module top_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [1:0]  counter,
  input  logic [1:0]  count,
  input  logic [2:0]  decoder_in,
  input  logic [7:0]  decoder_out,
  input  logic [15:0] decoder_out_16,
  input  logic [15:0] out
);

  default clocking @(posedge clk); endclocking
  default disable iff (reset);

  // Sync reset and up-counter behavior
  a_reset_zero:  assert property (@(posedge clk) reset |-> (counter==2'b00 && count==2'b00));
  a_count_alias: assert property (count == counter);
  a_upcount:     assert property ((!reset && !$past(reset)) |-> counter == $past(counter)+2'd1);

  // Decoder interface and function
  a_dec_in_zext: assert property (decoder_in == {1'b0, counter});
  a_dec_func:    assert property (decoder_out == (8'b1 << decoder_in));
  a_dec_onehot:  assert property ($onehot(decoder_out));

  // 4x expansion wiring to 16-bit
  a_out16_build: assert property (
                    decoder_out_16 == { {4{decoder_out[0]}},
                                        {4{decoder_out[1]}},
                                        {4{decoder_out[2]}},
                                        {4{decoder_out[3]}} } );

  // Registered output: one-cycle delayed mapping from count
  function automatic logic [15:0] exp16(input logic [1:0] c);
    case (c)
      2'd0: exp16 = 16'hF000;
      2'd1: exp16 = 16'h0F00;
      2'd2: exp16 = 16'h00F0;
      default: exp16 = 16'h000F;
    endcase
  endfunction
  a_out_map:      assert property ((!reset && !$past(reset)) |-> out == exp16($past(count)));
  a_out_four:     assert property ($countones(out)==4);

  // X/Z sanitization after reset release
  a_no_x:         assert property (
                      !$isunknown(counter) && !$isunknown(count) &&
                      !$isunknown(decoder_out) && !$isunknown(out));

  // Compact functional coverage
  c_full_cycle:   cover property (count==2'd0 ##1 2'd1 ##1 2'd2 ##1 2'd3 ##1 2'd0);
  c_out_vals0:    cover property (out==16'hF000);
  c_out_vals1:    cover property (out==16'h0F00);
  c_out_vals2:    cover property (out==16'h00F0);
  c_out_vals3:    cover property (out==16'h000F);

endmodule

bind top_module top_sva u_top_sva (
  .clk(clk),
  .reset(reset),
  .counter(counter),
  .count(count),
  .decoder_in(decoder_in),
  .decoder_out(decoder_out),
  .decoder_out_16(decoder_out_16),
  .out(out)
);