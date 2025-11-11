// SVA for shift_register
// Bindable, concise, priority-accurate, with essential coverage

module shift_register_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        load,
  input  logic        shift,
  input  logic [7:0]  data_in,
  input  logic [7:0]  parallel_in,
  input  logic [7:0]  data_out
);

  default clocking cb @(posedge clk); endclocking

  // Guard $past at time 0
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Sanity (no X on controls/output)
  assert property (!$isunknown({reset, load, shift})); 
  assert property (!$isunknown(data_out));

  // Functional correctness and priority
  assert property (reset |=> data_out == 8'h00);
  assert property (!reset && load                    |=> data_out == $past(parallel_in)); // load has priority over shift
  assert property (!reset && !load && shift          |=> data_out == { $past(data_out[6:0]), 1'b0 }); // zero-fill left shift by 1
  assert property (!reset && !load && !shift         |=> data_out == $past(data_in)); // default path

  // Strong multi-cycle semantic check: 8 shifts zero the register
  assert property (((!reset && !load && shift)[*8])  |=> data_out == 8'h00);

  // Coverage: exercise all behaviors and a contention case
  cover property (reset |=> data_out == 8'h00);
  cover property (!reset && load                    |=> data_out == $past(parallel_in));
  cover property (!reset && !load && shift          |=> data_out == { $past(data_out[6:0]), 1'b0 });
  cover property (!reset && !load && !shift         |=> data_out == $past(data_in));
  cover property (!reset && load && shift           |=> data_out == $past(parallel_in)); // load-over-shift
  cover property (((!reset && !load && shift)[*8])  |=> data_out == 8'h00);

endmodule

// Bind to the DUT
bind shift_register shift_register_sva i_shift_register_sva (
  .clk        (clk),
  .reset      (reset),
  .load       (load),
  .shift      (shift),
  .data_in    (data_in),
  .parallel_in(parallel_in),
  .data_out   (data_out)
);