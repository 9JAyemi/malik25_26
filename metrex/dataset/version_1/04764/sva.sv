// SVA for top_module
// Bind into the DUT to access internal signals.
module top_module_sva(
  input logic               clk,
  input logic               reset,
  input logic               d,
  input logic               select,
  input logic [4:0]         in,
  input logic               out_and, out_or, out_nor,
  input logic [2:0]         final_output,
  // internal signals
  input logic [2:0]         shift_reg,
  input logic [2:0]         shift_reg_out,
  input logic [2:0]         mux_out,
  input logic [3:0]         decoder_out,
  input logic               and_out, or_out, nor_out
);
  default clocking cb @(posedge clk); endclocking

  // Reset and shift-register behavior
  a_reset_clears: assert property (reset |-> shift_reg == 3'b000);
  a_shift_step:   assert property (disable iff (reset)
                                  shift_reg == { $past(shift_reg[1:0],1,reset), d });

  // Internal wiring sanity
  a_shift_out_match: assert property (shift_reg_out == shift_reg);

  // Mux behavior (note truncation in RHS concatenations)
  a_mux_sel0: assert property (!select |-> mux_out == in[2:0]);
  a_mux_sel1: assert property ( select |-> mux_out == 3'b000);

  // Final output selection
  a_final_sel0: assert property (!select |-> final_output == mux_out);
  a_final_sel1: assert property ( select |-> final_output == {and_out, or_out, nor_out});

  // 5-input logic gate equivalences and consistency
  a_and_equiv:  assert property (out_and == and_out && out_and == &in);
  a_or_equiv:   assert property (out_or  == or_out  && out_or  == |in);
  a_nor_equiv:  assert property (out_nor == nor_out && out_nor == ~|in);
  a_nor_not_or: assert property (out_nor == ~out_or);
  a_and_implies_or: assert property (out_and |-> out_or);
  a_mutual_excl:    assert property (!(out_and && out_nor));

  // Decoder truth table
  a_dec_0: assert property (!in[4] |-> decoder_out == 4'b0001);
  a_dec_1: assert property ( in[4] |-> decoder_out == 4'b1110);

  // No X on primary outputs
  a_no_x_outs: assert property (!$isunknown({out_and, out_or, out_nor, final_output}));

  // Coverage
  c_reset_deassert:   cover property (reset ##1 !reset);
  c_shift_101:        cover property (disable iff (reset) d ##1 !d ##1 d ##0 shift_reg == 3'b101);
  c_sel0_nonzero:     cover property (!select && in[2:0] != 3'b000 && mux_out == in[2:0] && final_output == mux_out);
  c_sel1_path:        cover property ( select && final_output == {out_and, out_or, out_nor});
  c_all_zeros:        cover property (in == 5'b00000 && out_nor && !out_or && !out_and);
  c_all_ones:         cover property (in == 5'b11111 && out_and && out_or && !out_nor);
  c_decoder_both:     cover property (!in[4] && decoder_out == 4'b0001);
  c_decoder_both2:    cover property ( in[4] && decoder_out == 4'b1110);
endmodule

bind top_module top_module_sva sva_bind(
  .clk(clk),
  .reset(reset),
  .d(d),
  .select(select),
  .in(in),
  .out_and(out_and),
  .out_or(out_or),
  .out_nor(out_nor),
  .final_output(final_output),
  .shift_reg(shift_reg),
  .shift_reg_out(shift_reg_out),
  .mux_out(mux_out),
  .decoder_out(decoder_out),
  .and_out(and_out),
  .or_out(or_out),
  .nor_out(nor_out)
);