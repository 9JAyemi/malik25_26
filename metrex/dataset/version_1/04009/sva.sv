// SVA for InputSync: validate 3-cycle pipeline behavior and basic coverage

checker inputsync_chk (input logic CLK_I, D_I, D_O);
  default clocking @(posedge CLK_I); endclocking

  // Core functionality: output equals input delayed by 3 clocks
  a_delay3: assert property (1'b1 |-> ##3 (D_O == $past(D_I,3)));

  // No X on output once the last 3 samples of D_I are known
  a_no_x_after3: assert property (
    !$isunknown($past(D_I,1)) && !$isunknown($past(D_I,2)) && !$isunknown($past(D_I,3))
    |-> !$isunknown(D_O)
  );

  // Coverage: rising and falling edges propagate with 3-cycle latency
  c_rise: cover property ($rose(D_I) ##3 $rose(D_O));
  c_fall: cover property ($fell(D_I) ##3 $fell(D_O));
endchecker

// Bind to every instance of the single-bit synchronizer
bind InputSync inputsync_chk (.*);

// Optional bus-level checker (bind to your 4-bit wrapper if desired)
checker bus_sync_chk #(int W=4) (input logic CLK_I, input logic [W-1:0] D_I, input logic [W-1:0] D_O);
  default clocking @(posedge CLK_I); endclocking
  a_bus_delay3: assert property (1'b1 |-> ##3 (D_O == $past(D_I,3)));
  c_bus_activity: cover property ((D_I != $past(D_I)) ##3 (D_O != $past(D_O)));
endchecker
// Example bind (edit module/port names if your top has different identifiers):
// bind <top_module_name> bus_sync_chk #(.W(4)) (.CLK_I(CLK_I), .D_I(D_I), .D_O(D_O));