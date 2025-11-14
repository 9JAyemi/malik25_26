// SVA for rotator: concise, high-quality checks and functional coverage
module rotator_sva (
    input  logic         clk,
    input  logic         load,
    input  logic [1:0]   ena,
    input  logic [99:0]  data,
    input  logic [99:0]  q
);
  default clocking cb @(posedge clk); endclocking

  // past-valid guard (no reset present)
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // helper functions
  function automatic logic [99:0] rotR1 (input logic [99:0] v);
    rotR1 = {v[0], v[99:1]}; // rotate-right by 1
  endfunction
  function automatic logic [99:0] asr1 (input logic [99:0] v);
    asr1 = {v[99], v[99:1]}; // arithmetic shift-right by 1
  endfunction

  // Assertions: behavior per spec
  // load dominates
  assert property (load |=> q == $past(data))
    else $error("rotator: load did not capture data");

  // ena = 2'b00: rotate-right by 1
  assert property (!load && (ena == 2'b00) |=> q == rotR1($past(q)))
    else $error("rotator: ena=00 rotate-right mismatch");

  // ena = 2'b10: rotate-right by 1 (identical to 2'b00)
  assert property (!load && (ena == 2'b10) |=> q == rotR1($past(q)))
    else $error("rotator: ena=10 rotate-right mismatch");

  // ena = 2'b01: arithmetic shift-right by 1 (MSB retained)
  assert property (!load && (ena == 2'b01) |=> q == asr1($past(q)))
    else $error("rotator: ena=01 arithmetic shift-right mismatch");

  // ena = 2'b11: hold
  assert property (!load && (ena == 2'b11) |=> q == $past(q))
    else $error("rotator: ena=11 did not hold value");

  // Minimal functional coverage
  cover property (load);                       // exercised load
  cover property (!load && (ena == 2'b00));    // mode 00 seen
  cover property (!load && (ena == 2'b01));    // mode 01 seen
  cover property (!load && (ena == 2'b10));    // mode 10 seen
  cover property (!load && (ena == 2'b11));    // mode 11 seen

  // Edge-behavior coverage
  // rotate-right brings LSB to MSB
  cover property (!load && (ena inside {2'b00,2'b10}) |=> (q[99] == $past(q[0])));
  // arithmetic shift retains MSB (sign)
  cover property (!load && (ena == 2'b01) |=> (q[99] == $past(q[99])));

endmodule

// Bind into DUT
bind rotator rotator_sva rotator_sva_i (.clk(clk), .load(load), .ena(ena), .data(data), .q(q));