// SVA for pipeline_register
// Concise, high-quality checks and coverage

module pipeline_register_sva #(parameter width = 8)
(
  input logic                 clk,
  input logic                 reset,
  input logic [width-1:0]     data_in,
  input logic [width-1:0]     data_out
);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity: reset must be known at sampling
  a_reset_known: assert property (@cb !$isunknown(reset));

  // Functional spec: 1-cycle latency with synchronous reset dominance
  // After the first sampled cycle, current data_out must equal:
  //   0 if reset was 1 last cycle, else last cycle's data_in.
  a_functional: assert property (@cb
    $past(1'b1) |-> (data_out == ($past(reset) ? '0 : $past(data_in)))
  );

  // While reset is held across cycles, output must be 0
  a_reset_holds_zero: assert property (@cb
    reset && $past(reset) |-> (data_out == '0)
  );

  // Coverage: reset clears output to 0 on the next cycle
  c_reset_clears: cover property (@cb
    reset ##1 (data_out == '0)
  );

  // Coverage: non-zero data passes through in one cycle when not in reset
  c_pass_nonzero: cover property (@cb
    !reset && (data_in != '0) ##1 (data_out == $past(data_in) && data_out != '0)
  );

  // Coverage: back-to-back transfers with changing data
  c_back_to_back: cover property (@cb
    !reset && $changed(data_in) ##1 (data_out == $past(data_in))
    ##1 $changed(data_in)       ##1 (data_out == $past(data_in))
  );

  // Coverage: all-ones pattern transfers
  c_pass_all_ones: cover property (@cb
    !reset && (data_in == '1) ##1 (data_out == $past(data_in))
  );

endmodule

// Bind assertions to the DUT
bind pipeline_register pipeline_register_sva #(.width(width)) u_pipeline_register_sva
(
  .clk     (clk),
  .reset   (reset),
  .data_in (data_in),
  .data_out(data_out)
);