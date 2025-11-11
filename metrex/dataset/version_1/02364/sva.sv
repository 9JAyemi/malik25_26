// SVA for barrel_shifter
module barrel_shifter_sva (
  input logic        clk,
  input logic        reset,
  input logic [31:0] data,
  input logic [31:0] shift_amount,
  input logic [31:0] shifted_data
);

  // Reset behavior
  assert property (@(posedge clk) reset |=> shifted_data == 32'h0);

  // No X/Z on output when not in reset
  assert property (@(posedge clk) disable iff (reset) !$isunknown(shifted_data));

  // Core functional check: 1-cycle latency, logical left shift for any non-zero amount.
  // Amount >= 32 yields 0. Amount == 0 is pass-through.
  assert property (@(posedge clk) disable iff (reset)
    $past(!reset) && !$isunknown($past({data,shift_amount})) |->
      ( $past(shift_amount) == 32'd0
        ? (shifted_data == $past(data))
        : (shifted_data ==
            ( ($past(shift_amount) >= 32) ? 32'h0
              : ($past(data) << $past(shift_amount[4:0])) ))
      )
  );

  // Sanity: any non-zero unsigned shift_amount must be > 0 (dead "else" branch in DUT)
  assert property (@(posedge clk) disable iff (reset)
    (shift_amount != 0) |-> (shift_amount > 0)
  );

  // Functional coverage
  cover property (@(posedge clk) reset ##1 !reset);                  // reset sequence
  cover property (@(posedge clk) disable iff (reset) $past(!reset) && $past(shift_amount)==0);
  cover property (@(posedge clk) disable iff (reset) $past(!reset) && $past(shift_amount)==1);
  cover property (@(posedge clk) disable iff (reset) $past(!reset) && $past(shift_amount)==31);
  cover property (@(posedge clk) disable iff (reset) $past(!reset) && $past(shift_amount)>=32);
  cover property (@(posedge clk) disable iff (reset) $past(!reset) && $past(data)==32'h0000_0001);
  cover property (@(posedge clk) disable iff (reset) $past(!reset) && $past(data)==32'h8000_0000);

endmodule

// Bind into DUT
bind barrel_shifter barrel_shifter_sva i_barrel_shifter_sva (
  .clk(clk),
  .reset(reset),
  .data(data),
  .shift_amount(shift_amount),
  .shifted_data(shifted_data)
);