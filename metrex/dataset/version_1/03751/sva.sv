// SVA for shift_register: concise, high-quality checks and useful coverage.
// Bind this module to the DUT instance(s).

module shift_register_sva (
  input logic        clk,
  input logic        load,
  input logic [3:0]  data_in,
  input logic [3:0]  data_out
);

  // guard $past at time 0
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Load wins: on load, capture data_in
  assert property (load |-> data_out == $past(data_in))
    else $error("Load did not capture data_in");

  // Rotate-left by 1 when not loading
  assert property (!load |-> data_out == { $past(data_out)[2:0], $past(data_out)[3] })
    else $error("Rotate-left behavior violated");

  // 4-cycle periodicity when not loading (rotate-left by 4 returns to original)
  assert property (!load[*4] |-> data_out == $past(data_out,4))
    else $error("4-cycle rotation periodicity violated");

  // Clean output (no X/Z) after first sampled cycle
  assert property (!$isunknown(data_out))
    else $error("data_out has X/Z");

  // Coverage: observe a load that takes effect next cycle
  cover property (load ##1 data_out == $past(data_in));

  // Coverage: see at least one rotation step
  cover property (!load ##1 data_out == { $past(data_out)[2:0], $past(data_out)[3] });

  // Coverage: load then 4 rotates return to the loaded value
  cover property (load ##1 !load[*4] ##0 (data_out == $past(data_in,5)));

  // Coverage: demonstrate bit walks through all positions (orientation check)
  cover property (
    load && data_in == 4'b0001
    ##1 !load && data_out == 4'b0010
    ##1 !load && data_out == 4'b0100
    ##1 !load && data_out == 4'b1000
    ##1 !load && data_out == 4'b0001
  );

endmodule

// Example bind (place in a TB or a separate SVA file):
// bind shift_register shift_register_sva u_shift_register_sva (.*);