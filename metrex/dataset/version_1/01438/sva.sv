// SVA for nios_altmemddr_0_ex_lfsr8
// Concise checks for reset/enable/load/pause priority, next-state function, and coverage.
// Bind this module to the DUT instance in your testbench.

module nios_altmemddr_0_ex_lfsr8_sva
  #(parameter int unsigned seed = 32)
  (
    input  logic        clk,
    input  logic        reset_n,
    input  logic        enable,
    input  logic        pause,
    input  logic        load,
    input  logic [7:0]  data,
    input  logic [7:0]  ldata,
    input  logic [7:0]  lfsr_data // internal reg from DUT (for tie-off check)
  );

  localparam logic [7:0] SEED8 = seed[7:0];

  // Next-state function for this 8-bit LFSR
  function automatic logic [7:0] nxt(input logic [7:0] s);
    nxt = { s[6], s[5], s[4], (s[3]^s[7]), (s[2]^s[7]), (s[1]^s[7]), s[0], s[7] };
  endfunction

  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  assert property (cb !$isunknown({reset_n, enable, pause, load})))
    else $error("Control inputs have X/Z");

  assert property (cb !$isunknown(data))
    else $error("Output data has X/Z");

  // data is tied to internal lfsr_data
  assert property (cb data == lfsr_data)
    else $error("data != lfsr_data");

  // Asynchronous reset drives seed value while reset_n==0
  assert property (cb !reset_n |-> (data == SEED8))
    else $error("Async reset not forcing SEED8");

  // When enable==0, next cycle must be seed (regardless of load/pause)
  assert property (cb reset_n && !enable |=> (data == SEED8))
    else $error("!enable did not force SEED8 next cycle");

  // Load has priority over pause; when enabled+load, capture ldata next cycle
  assert property (cb reset_n && enable && load |-> !$isunknown(ldata))
    else $error("ldata is X/Z when load is asserted");
  assert property (cb reset_n && enable && load |=> (data == ldata))
    else $error("Load did not capture ldata next cycle");

  // When enabled, no load, and not paused: perform exact LFSR step
  assert property (cb reset_n && enable && !load && !pause |=> (data == nxt($past(data))))
    else $error("LFSR next-state mismatch");

  // When enabled, no load, and paused: hold value
  assert property (cb reset_n && enable && !load && pause |=> (data == $past(data)))
    else $error("Pause did not hold data");

  // Minimal functional coverage
  cover property (cb !reset_n);                                   // async reset observed
  cover property (cb reset_n && !enable ##1 (data == SEED8));     // seeding on !enable
  cover property (cb reset_n && enable && load && !pause);        // load without pause
  cover property (cb reset_n && enable && load && pause);         // load with pause (priority)
  cover property (cb reset_n && enable && !load && !pause ##1 (data == nxt($past(data)))); // shift
  cover property (cb reset_n && enable && !load && pause ##1 (data == $past(data)));       // hold

endmodule

// Example bind (place in your testbench or a bind file):
// bind nios_altmemddr_0_ex_lfsr8
//   nios_altmemddr_0_ex_lfsr8_sva #(.seed(seed)) sva (.*);