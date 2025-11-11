// Add this SVA block inside module shift_register (or bind it to the instance)
`ifndef SYNTHESIS
// Default sampling clock
default clocking cb @(posedge clk); endclocking

// Track when $past() is valid and when 4-cycle history exists
logic past_valid;
int unsigned cycles;
initial begin past_valid = 1'b0; cycles = 0; end
always @(posedge clk) begin past_valid <= 1'b1; cycles <= cycles + 1; end

// Next-state of reg1 matches RTL mux
assert property (disable iff(!past_valid)
  reg1 == ($past(parallel_load) ? $past(in) : $past(reg1)));

// Shift chain and output latency (1-cycle each stage)
assert property (disable iff(!past_valid)
  (reg2 == $past(reg1)) && (reg3 == $past(reg2)) && (reg4 == $past(reg3)) && (out == $past(reg4)));

// End-to-end: a load produces the sampled input at out 4 cycles later
assert property (disable iff(cycles < 4)
  parallel_load |-> ##4 (out == $past(in,4)));

// Coverage: single load observed at output after 4 cycles
cover property (disable iff(cycles < 4)
  parallel_load ##4 (out == $past(in,4)));

// Coverage: two back-to-back loads produce two back-to-back outputs 4 cycles later
cover property (disable iff(cycles < 5)
  parallel_load ##1 parallel_load ##4 (out == $past(in,4)) ##1 (out == $past(in,5)));
`endif