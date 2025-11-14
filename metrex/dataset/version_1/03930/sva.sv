// SVA for shift_register. Bind this file to the DUT.
// Note: As coded, {shift_reg[6:0], data_in} is 15 bits feeding an 8-bit reg,
// so the effective next value is just data_in[7:0]. A warning and matching check are provided.

module shift_register_sva (
  input clk,
  input reset,
  input clear,
  input [7:0] data_in,
  input [7:0] data_out
);

  // Reset behavior (dominates clear)
  assert property (@(posedge clk) reset |=> data_out == 8'h00);
  assert property (@(posedge clk) (reset && clear) |=> data_out == 8'h00);

  // Clear behavior when not in reset
  assert property (@(posedge clk) (!reset && clear) |=> data_out == 8'hFF);

  // Update behavior when neither reset nor clear
  generate
    if ($bits(data_in) == 1) begin : serial_shift_intent
      // If data_in were 1-bit, typical shift-right with serial in:
      assert property (@(posedge clk)
        (!reset && !clear) |=> data_out == { $past(data_out[6:0]), $past(data_in) }
      );
    end else begin : coded_behavior
      // As coded, RHS truncates; next value equals previous data_in.
      initial $warning("shift_register: data_in is %0d bits; concatenation truncates and simply loads data_in. Check intent.", $bits(data_in));
      assert property (@(posedge clk)
        (!reset && !clear) |=> data_out == $past(data_in)
      );
    end
  endgenerate

  // Minimal functional coverage
  cover property (@(posedge clk) reset ##1 !reset);                // reset pulse
  cover property (@(posedge clk) (!reset && clear));               // clear event
  cover property (@(posedge clk) (!reset && !clear));              // update/shift path
  cover property (@(posedge clk) (reset && clear));                // simultaneous reset & clear

endmodule

bind shift_register shift_register_sva sva(.clk(clk), .reset(reset), .clear(clear), .data_in(data_in), .data_out(data_out));