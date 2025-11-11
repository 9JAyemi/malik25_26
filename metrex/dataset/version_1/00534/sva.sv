// SVA checker for top_module
module top_module_sva(
    input clk,
    input async_reset,
    input [1:0] ena,
    input [99:0] data,
    input [3:0] q,
    input [99:0] q_out
);

  // Past-valid flags to avoid first-sample $past hazards
  logic past_valid_pos, past_valid_neg;
  always_ff @(posedge clk or posedge async_reset) begin
    if (async_reset) past_valid_pos <= 1'b0;
    else             past_valid_pos <= 1'b1;
  end
  always_ff @(negedge clk or posedge async_reset) begin
    if (async_reset) past_valid_neg <= 1'b0;
    else             past_valid_neg <= 1'b1;
  end

  // Counter/reset behavior checked via q[2:0]; MSB must be 0 due to width-extension
  // Reset dominates counter on posedge clk
  assert property (@(posedge clk) async_reset |-> ##0 (q[2:0] == 3'd0 && q[3] == 1'b0));

  // Increment when enabled (non-wrap)
  assert property (@(posedge clk)
    disable iff (async_reset)
    past_valid_pos && ena[0] && ($past(q[2:0]) != 3'd7)
    |-> ##0 (q[2:0] == $past(q[2:0]) + 3'd1)
  );

  // Wrap from 7 -> 0 when enabled
  assert property (@(posedge clk)
    disable iff (async_reset)
    past_valid_pos && ena[0] && ($past(q[2:0]) == 3'd7)
    |-> ##0 (q[2:0] == 3'd0)
  );

  // Hold when not enabled
  assert property (@(posedge clk)
    disable iff (async_reset)
    past_valid_pos && !ena[0]
    |-> ##0 (q[2:0] == $past(q[2:0]))
  );

  // q[3] must always be 0
  assert property (@(posedge clk)  ##0 (q[3] == 1'b0));
  assert property (@(negedge clk) ##0 (q[3] == 1'b0));

  // Functional sum on negedge clk
  wire [49:0] lo = data[49:0];
  wire [49:0] hi = data[99:50];

  // Update when enabled: 51-bit sum, zero-extended into q_out[99:51]
  assert property (@(negedge clk)
    ena[1] |-> ##0 (q_out[50:0] == (lo + hi) && q_out[99:51] == '0)
  );

  // Hold when not enabled
  assert property (@(negedge clk)
    past_valid_neg && !ena[1] |-> ##0 $stable(q_out)
  );

  // ------------- Coverage -------------
  // See counter increment path after reset deassert
  cover property (@(posedge clk)
    !async_reset ##1 (ena[0]) ##1 (ena[0]) ##1 (ena[0])
  );

  // Wrap-around covered
  cover property (@(posedge clk)
    disable iff (async_reset)
    past_valid_pos && ($past(q[2:0]) == 3'd7) && ena[0] ##0 (q[2:0] == 3'd0)
  );

  // Sum update with carry into bit 50
  cover property (@(negedge clk)
    ena[1] ##0 q_out[50]
  );

  // Concurrent activity: both enables exercised (separately on their edges)
  cover property (@(posedge clk)  !async_reset && ena[0]);
  cover property (@(negedge clk)  ena[1]);

  // Reset and enable[0] high on same posedge (reset dominates)
  cover property (@(posedge clk) async_reset && ena[0]);

endmodule

// Bind into DUT
bind top_module top_module_sva sva_i (.*);