// SVA for register_4bit
module register_4bit_sva (
  input logic        clk,
  input logic        reset,
  input logic        enable,
  input logic [3:0]  data_in,
  input logic [3:0]  data_out
);
  default clocking cb @(posedge clk); endclocking

  // Core functional checks
  a_reset_clears_now:      assert property (reset                  |-> ##0 (data_out == 4'b0));
  a_reset_dominates:       assert property (reset && enable        |-> ##0 (data_out == 4'b0));
  a_load_on_enable:        assert property (!reset && enable       |-> ##0 (data_out == data_in));
  a_hold_when_disabled:    assert property (!reset && !enable      |=>       $stable(data_out));

  // No spurious change without a cause (change only when reset or enable at this edge)
  a_change_has_cause:      assert property (##0 (data_out != $past(data_out)) |-> (reset || enable));

  // Sanity/knownness
  a_ctrl_known:            assert property (!$isunknown({reset, enable}));
  a_out_known_after_act:   assert property ($past(reset || enable,1,1'b0) |-> !$isunknown(data_out));

  // Coverage
  c_reset_pulse:           cover  property (reset ##1 !reset);
  c_any_write:             cover  property (!reset && enable |-> ##0 (data_out == data_in));
  c_write_nonzero:         cover  property (!reset && enable && (data_in != 4'b0) |-> ##0 (data_out == data_in));
  c_hold_with_input_toggle:cover  property (!reset && !enable ##1 (!reset && !enable && (data_in != $past(data_in)) && $stable(data_out)));
  c_back_to_back_writes:   cover  property ((!reset && enable) ##1 (!reset && enable));

  // Cover all 16 written values
  genvar v;
  generate
    for (v = 0; v < 16; v++) begin : g_cover_vals
      cover property ($past(!reset && enable,1,1'b0) && (data_out == v[3:0]));
    end
  endgenerate
endmodule

bind register_4bit register_4bit_sva i_register_4bit_sva (
  .clk(clk),
  .reset(reset),
  .enable(enable),
  .data_in(data_in),
  .data_out(data_out)
);