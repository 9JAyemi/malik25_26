// SVA for the given design. Bind as shown at bottom.

module binary_counter_sva(input clk, input reset, input [3:0] count_out);
  default clocking cb @(posedge clk); endclocking

  // No Xs on clock edges
  assert property ( !$isunknown(count_out) );

  // Async reset takes effect immediately
  assert property (@(posedge reset) ##0 (count_out == 4'd0 && !$isunknown(count_out)));

  // While reset is high, output is 0
  assert property ( reset |-> count_out == 4'd0 );

  // Increment by 1 when not in reset and previous cycle not in reset
  assert property ( (!reset && !$past(reset)) |-> count_out == $past(count_out) + 1 );

  // First cycle after reset deasserts: counter goes to 1
  assert property ( $past(reset) && !reset |-> count_out == 4'd1 );

  // Coverage
  cover property ( $rose(reset) );
  cover property ( $fell(reset) );
  cover property ( !$past(reset) && !reset && $past(count_out)==4'hF && count_out==4'h0 );
endmodule

module top_module_sva(
  input clk, input reset,
  input [3:0] counter_out,
  input [7:0] data_in,
  input       parity_out,
  input [3:0] final_out
);
  default clocking cb @(posedge clk); endclocking

  // No Xs on observable outputs
  assert property ( !$isunknown(parity_out) && !$isunknown(final_out) );

  // Parity correctness (even parity)
  assert property ( parity_out == ~^data_in );

  // final_out = counter_out + parity_out (4-bit wrap)
  assert property ( final_out == ((counter_out + parity_out) & 4'hF) );

  // Coverage
  cover property ( parity_out == 1'b0 );
  cover property ( parity_out == 1'b1 );
  cover property ( !reset && counter_out==4'hF && parity_out && final_out==4'h0 );
endmodule

bind binary_counter binary_counter_sva bcsva(.clk(clk), .reset(reset), .count_out(count_out));
bind top_module     top_module_sva     tmsva(.clk(clk), .reset(reset),
                                             .counter_out(counter_out),
                                             .data_in(data_in),
                                             .parity_out(parity_out),
                                             .final_out(final_out));