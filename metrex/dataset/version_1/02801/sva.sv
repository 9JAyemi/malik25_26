// SVA for top_module
// Bindable checker that verifies reset, pipeline, mux, shift, AND, and output behavior.
// Also includes concise functional coverage.
module top_module_chk (
  input logic        clk,
  input logic        reset,
  input logic        select,
  input logic [15:0] in_A,
  input logic [15:0] in_B,
  input logic [15:0] reg_in,
  input logic [15:0] shift_out,
  input logic [15:0] mux_out,
  input logic [15:0] and_out,
  input logic [7:0]  out
);

  // Basic X/Z sanitation on sampled interface and key internals
  assert property (@(posedge clk) !$isunknown({reset,select,in_A,in_B}));
  assert property (@(posedge clk) !$isunknown({reg_in,shift_out,mux_out,and_out,out}));

  // Asynchronous reset effect must be visible on the sampling clock
  assert property (@(posedge clk) reset |-> (reg_in == 16'h0000));

  // Register load: reg_in captures in_A each cycle when not in reset
  assert property (@(posedge clk) !reset |-> (reg_in == $past(in_A,1,16'h0000)));

  // Combinational equivalences
  assert property (@(posedge clk) shift_out == (reg_in << select));
  // This will catch the width bug in temp_mux_out/mux_out implementation
  assert property (@(posedge clk) mux_out   == (select ? in_B : in_A));
  assert property (@(posedge clk) and_out   == (mux_out & shift_out));

  // Output register: out is one-cycle delayed and_out[7:0]
  assert property (@(posedge clk) out == $past(and_out[7:0],1,8'h00));

  // End-to-end functional pipeline check (concise)
  // out(t) == [ ((select?in_B:in_A) & (prev(in_A) << select)) at t-1 ][7:0]
  assert property (@(posedge clk)
    out == $past( (((select ? in_B : in_A) & ($past(in_A,1,16'h0000) << select))[7:0]), 1, 8'h00 )
  );

  // Minimal functional coverage
  cover property (@(posedge clk) reset ##1 !reset);
  cover property (@(posedge clk) select == 0 ##1 select == 1);
  cover property (@(posedge clk) select == 1 ##1 select == 0);
  cover property (@(posedge clk) (and_out != 16'h0000) ##1 (out != 8'h00));
endmodule

// Bind the checker to the DUT, including internal signals
bind top_module top_module_chk u_top_module_chk (
  .clk      (clk),
  .reset    (reset),
  .select   (select),
  .in_A     (in_A),
  .in_B     (in_B),
  .reg_in   (reg_in),
  .shift_out(shift_out),
  .mux_out  (mux_out),
  .and_out  (and_out),
  .out      (out)
);