// SVA checker for shift_register
module shift_register_sva (
    input  logic        clk,
    input  logic        serial_in,
    input  logic        reset,        // active-high functional enable, active-low clear in DUT (!reset clears)
    input  logic [3:0]  parallel_out,
    // bind these to DUT internals
    input  logic [3:0]  pipeline0,
    input  logic [3:0]  pipeline1,
    input  logic [3:0]  pipeline2
);

  // guard for $past usage on posedge domain
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // pipeline shifts on posedge: new values equal previous stage
  assert property (@(posedge clk) past_valid |-> (pipeline0 == $past(serial_in)));
  assert property (@(posedge clk) past_valid |-> (pipeline1 == $past(pipeline0)));
  assert property (@(posedge clk) past_valid |-> (pipeline2 == $past(pipeline1)));

  // pipeline must not update on negedge; output must not update on posedge
  assert property (@(negedge clk) ##0 ($stable(pipeline0) && $stable(pipeline1) && $stable(pipeline2)));
  assert property (@(posedge clk) ##0 $stable(parallel_out));

  // functional update at negedge: reset low clears, otherwise pass pipeline2
  assert property (@(negedge clk) ##0 (reset ? (parallel_out == pipeline2) : (parallel_out == 4'h0)));

  // end-to-end latency: when enabled, output equals serial_in from 2 prior posedges (zero-extended)
  assert property (@(negedge clk) reset |-> ##0 (parallel_out == {3'b0, $past(serial_in, 2, posedge clk)}));

  // value domain: internal stages and output should be 4'h0 or 4'h1 (flags X/Z and width/extension issues)
  assert property (@(posedge clk) past_valid |-> (pipeline0 inside {4'h0,4'h1}) &&
                                           (pipeline1 inside {4'h0,4'h1}) &&
                                           (pipeline2 inside {4'h0,4'h1}));
  assert property (@(negedge clk) reset |-> ##0 (parallel_out inside {4'h0,4'h1}));

  // Coverage
  cover property (@(negedge clk) !reset ##1 reset);                         // observe reset low->high
  cover property (@(posedge clk) pipeline2 == 4'h1);                         // a '1' reached the last stage
  cover property (@(negedge clk) reset && ##0 (parallel_out == 4'h1));      // output observes a '1'
  cover property (@(negedge clk) reset && ##0 (parallel_out == 4'h0));      // output observes a '0'
endmodule

// Bind example (place in a testbench or a separate bind file)
// bind shift_register shift_register_sva sva (.*,
//   .pipeline0(pipeline[0]),
//   .pipeline1(pipeline[1]),
//   .pipeline2(pipeline[2])
// );