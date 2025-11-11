// SVA for myModule — concise but comprehensive
module myModule_sva (
  input logic              CLK,
  input logic              reset,
  input logic              ready_downstream,
  input logic              ready,
  input logic              too_soon,
  input logic [31:0]       output_count,
  input logic [64:0]       process_input,
  input logic [64:0]       process_output
);
  localparam int THRESH = 76800;

  // Clocking
  default clocking cb @(posedge CLK); endclocking

  // Basic reset behavior
  assert property (reset |=> ready==1'b0 && output_count==32'd0 && process_output==65'd0);

  // too_soon gate must force stall and hold data/counter
  assert property (!reset && too_soon |=> ready==1'b0
                                     && output_count==$past(output_count)
                                     && process_output==$past(process_output));

  // When not reset and not too_soon, counter must increment every cycle
  assert property (!reset && !too_soon |=> output_count == $past(output_count)+1);

  // Ready behavior
  assert property (!reset && !too_soon |=> ready==1'b1);
  assert property (reset || too_soon |=> ready==1'b0);

  // Functional effects when ready_downstream && output_count < THRESH
  // process_output becomes constant 65'd1 (LSB=1, others 0)
  assert property (!reset && !too_soon && ready_downstream && (output_count < THRESH)
                   |=> ready==1'b1 && process_output==65'd1);

  // Functional effects in the "else" path:
  // either !ready_downstream or output_count >= THRESH
  // process_output <= {1'b1, process_input[63:0]}
  assert property (!reset && !too_soon && (!ready_downstream || (output_count >= THRESH))
                   |=> ready==1'b1
                    && process_output[64]==1'b1
                    && process_output[63:0]==$past(process_input[63:0]));

  // Monotonic non-decreasing counter outside reset
  assert property (!reset |-> output_count >= $past(output_count));

  // Intent check: too_soon should reflect process_input[64] (likely intended behavior)
  assert property (!reset |-> (too_soon === process_input[64]));

  // Coverage: hit each control path
  cover property (reset);
  cover property (!reset && too_soon);
  cover property (!reset && !too_soon && ready_downstream && (output_count < THRESH));
  cover property (!reset && !too_soon && !ready_downstream);
  // Threshold crossing then else-path
  cover property (!reset && !too_soon && ready_downstream && output_count==THRESH-1
                  ##1 !reset && !too_soon && ready_downstream && output_count>=THRESH);
endmodule

// Bind into DUT
bind myModule myModule_sva sva_i (
  .CLK(CLK),
  .reset(reset),
  .ready_downstream(ready_downstream),
  .ready(ready),
  .too_soon(too_soon),
  .output_count(output_count),
  .process_input(process_input),
  .process_output(process_output)
);