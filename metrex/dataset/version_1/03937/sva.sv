// SVA for the given design. Bind these modules to the DUT instances.

////////////////////////////////////////
// rotator assertions
////////////////////////////////////////
module rotator_sva (
  input clk,
  input load,
  input [1:0] ena,
  input [99:0] data,
  input [99:0] out
);
  default clocking cb @(posedge clk); endclocking

  // Control not X
  a_ctrl_known: assert property (!$isunknown({load,ena}));

  // Load wins
  a_load: assert property (load |=> out == $past(data));

  // Rotate behaviors when not loading
  a_rl1:  assert property (!load && ena==2'b00 |=> out == {$past(out)[98:0], $past(out)[99]});
  a_rl2:  assert property (!load && ena==2'b01 |=> out == {$past(out)[1:0],  $past(out)[99:2]});
  a_rr1:  assert property (!load && ena==2'b10 |=> out == {$past(out)[0],    $past(out)[99:1]});
  a_hold: assert property (!load && ena==2'b11 |=> out == $past(out));

  // Basic coverage of each mode
  c_load: cover property (load);
  c_rl1:  cover property (!load && ena==2'b00);
  c_rl2:  cover property (!load && ena==2'b01);
  c_rr1:  cover property (!load && ena==2'b10);
  c_hold: cover property (!load && ena==2'b11);
endmodule

bind rotator rotator_sva(.clk(clk), .load(load), .ena(ena), .data(data), .out(out));


////////////////////////////////////////
// transition_detector assertions
////////////////////////////////////////
module transition_detector_sva (
  input clk,
  input reset,
  input [31:0] in,
  input out
);
  default clocking cb @(posedge clk); endclocking

  // Reset not X
  a_rst_known: assert property (!$isunknown(reset));

  // Async reset observed at clock edges: output forced low
  a_reset_low_out0: assert property (!reset |-> out==1'b0);

  // After 2 clean cycles post-reset, out == OR-reduction of delayed rising edges
  a_rise_delayed: assert property (
    reset && $past(reset,1) && $past(reset,2)
    |-> out == (($past(in,1) & ~$past(in,2)) != 0)
  );

  // No false positives when no rises in previous window
  a_no_fp: assert property (
    reset && $past(reset,1) && $past(reset,2)
    && (($past(in,1) & ~$past(in,2)) == 0)
    |-> out==1'b0
  );

  // Coverage: see at least one detected rise and at least one quiet cycle
  c_out1:   cover property (reset && $past(reset,2) && out);
  c_quiet0: cover property (reset && $past(reset,2) && $stable(in) |=> out==1'b0);
endmodule

bind transition_detector transition_detector_sva(.clk(clk), .reset(reset), .in(in), .out(out));


////////////////////////////////////////
// functional_module assertions (combinational mapping)
////////////////////////////////////////
module functional_module_sva (
  input [99:0] rotator_out,
  input transition_detector_out,
  input [131:0] out
);
  // Immediate assertions for pure combinational mapping
  always_comb begin
    assert (out[131] == 1'b0);
    assert (out[130:31] == rotator_out);
    assert (out[30:1] == {30{transition_detector_out}});
    assert (out[0] == transition_detector_out);
    assert (out[30:0] == {31{transition_detector_out}});
  end
endmodule

bind functional_module functional_module_sva(.rotator_out(rotator_out),
                                             .transition_detector_out(transition_detector_out),
                                             .out(out));


////////////////////////////////////////
// top_module end-to-end checks
////////////////////////////////////////
module top_module_sva (
  input clk,
  input reset,
  input [99:0] rotator_out,
  input transition_detector_out,
  input [131:0] out
);
  default clocking cb @(posedge clk); endclocking

  // Consistent end-to-end mapping
  a_top_map: assert property (
    out[131]==1'b0
    && out[130:31]==rotator_out
    && out[30:1]=={30{transition_detector_out}}
    && out[0]==transition_detector_out
  );

  // During reset low, transition_detector_out=0 forces lower 31 bits to 0
  a_reset_low_zero_tail: assert property (!reset |-> out[30:0]==31'b0);

  // Cover both states of the replicated tail
  c_tail0: cover property (out[30:0]==31'b0);
  c_tail1: cover property (out[30:0]==31'h7FFFFFFF); // all ones
endmodule

bind top_module top_module_sva(.clk(clk),
                               .reset(reset),
                               .rotator_out(rotator_out),
                               .transition_detector_out(transition_detector_out),
                               .out(out));