// SVA for top_module and its sub-blocks
// Bindable, concise, and focused on key functional checks + coverage

module top_module_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic        load,
  input  logic [3:0]  in,
  input  logic [15:0] decoder_out,
  input  logic [15:0] shift_reg,
  input  logic [15:0] data_out,
  input  logic [3:0]  count
);

  default clocking cb @(posedge clk); endclocking

  // Decoder: exact function and one-hotness
  a_dec_eq:     assert property (decoder_out == (16'h1 << in));
  a_dec_1hot:   assert property ($onehot(decoder_out));

  // Shift register: async reset, load, shift-left-by-1 with 0-fill, and onehot0 invariant
  a_sr_async_rst: assert property (rst |-> shift_reg == 16'h0);
  a_sr_load:      assert property (disable iff (rst) load  |=> shift_reg == $past(decoder_out));
  a_sr_shift:     assert property (disable iff (rst) !load |=> shift_reg == {$past(shift_reg)[14:0], 1'b0});
  a_sr_onehot0:   assert property ($onehot0(shift_reg));

  // Counter: equals popcount(shift_reg), which is always 0 or 1 due to onehot0
  a_cnt_pop:  assert property (count == $countones(shift_reg));
  a_cnt_le1:  assert property (count <= 4'd1);

  // Top-level data_out is a 1-cycle registered copy of shift_reg (ignore reset cycles)
  a_dout_pipe: assert property (disable iff (rst) data_out == $past(shift_reg));

  // Coverage

  // See every one-hot position of the shift register
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : C_POS
      c_sr_pos: cover property (shift_reg == (16'h1 << i));
    end
  endgenerate

  // See a load followed by the expected load outcome
  c_load:  cover property (disable iff (rst) load ##1 (shift_reg == $past(decoder_out)));

  // See a shift step from a one-hot state
  c_shift: cover property (disable iff (rst) $onehot($past(shift_reg)) && !load ##1 $onehot(shift_reg));

endmodule

// Bind into DUT (has visibility to internals decoder_out and shift_reg)
bind top_module top_module_sva top_module_sva_i (
  .clk        (clk),
  .rst        (rst),
  .load       (load),
  .in         (in),
  .decoder_out(decoder_out),
  .shift_reg  (shift_reg),
  .data_out   (data_out),
  .count      (count)
);