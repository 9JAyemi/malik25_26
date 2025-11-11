// SVA for top_module, counter, comparator
`ifndef SVA_TOP_COUNTER_COMPARATOR
`define SVA_TOP_COUNTER_COMPARATOR

// ---------- top_module SVA ----------
module top_sva
(
  input logic        CLK,
  input logic        RESET,
  input logic [3:0]  counter_out_reg,
  input logic [3:0]  counter_out_next,
  input logic        comparator_out,
  input logic        final_output
);
  default clocking cb @(posedge CLK); endclocking

  // Reset drives the registered counter to 0 on next cycle
  assert property (RESET |=> counter_out_reg == 4'd0);

  // Registered copy equals 1-cycle-delayed counter output
  assert property ($past(1'b1) && !RESET |-> counter_out_reg == $past(counter_out_next));

  // Combinational equivalence for final_output
  assert property (final_output == (comparator_out && (counter_out_reg == 4'd9)));

  // No X on output when not in reset
  assert property (disable iff (RESET) !$isunknown(final_output));

  // Coverage
  cover property (disable iff (RESET) final_output);
  cover property (disable iff (RESET) (counter_out_reg == 4'd9 && comparator_out));
endmodule

bind top_module top_sva i_top_sva (
  .CLK(CLK),
  .RESET(RESET),
  .counter_out_reg(counter_out_reg),
  .counter_out_next(counter_out_next),
  .comparator_out(comparator_out),
  .final_output(final_output)
);

// ---------- counter SVA ----------
module counter_sva
(
  input logic        CLK,
  input logic        RESET,
  input logic        LOAD,
  input logic [3:0]  DATA,
  input logic [3:0]  out
);
  default clocking cb @(posedge CLK); endclocking

  // Reset dominates
  assert property (RESET |=> out == 4'd0);

  // Load behavior
  assert property ((!RESET && LOAD) |=> out == DATA);

  // Increment behavior (non-wrap)
  assert property ($past(1'b1) && !RESET && !LOAD && $past(out) != 4'hF |=> out == $past(out) + 4'd1);

  // Wrap from F to 0
  assert property ($past(1'b1) && !RESET && !LOAD && $past(out) == 4'hF |=> out == 4'h0);

  // No X on output when not in reset
  assert property (disable iff (RESET) !$isunknown(out));

  // Coverage
  cover property (RESET ##1 !RESET);
  cover property ((!RESET && LOAD) ##1 (out == DATA));
  cover property ((!RESET && !LOAD && out == 4'hF) ##1 (out == 4'h0));
endmodule

bind counter counter_sva i_counter_sva (
  .CLK(CLK),
  .RESET(RESET),
  .LOAD(LOAD),
  .DATA(DATA),
  .out(out)
);

// ---------- comparator SVA ----------
module comparator_sva
(
  input logic [3:0] A,
  input logic [3:0] B,
  input logic       mode, // 1-bit
  input logic       out
);
  // Functional correctness for defined modes
  assert property ( (mode === 1'b0) |-> (out == (A == B)) );
  assert property ( (mode === 1'b1) |-> (out == (A >  B)) );

  // Output not X if inputs known
  assert property ( !$isunknown({A,B,mode}) |-> !$isunknown(out) );

  // Coverage: exercise both modes and outcomes
  cover property (mode==1'b0 && (A==B) && out);
  cover property (mode==1'b0 && (A!=B) && !out);
  cover property (mode==1'b1 && (A>B)  && out);
  cover property (mode==1'b1 && !(A>B) && !out);
endmodule

bind comparator comparator_sva i_comparator_sva (
  .A(A), .B(B), .mode(mode), .out(out)
);

`endif