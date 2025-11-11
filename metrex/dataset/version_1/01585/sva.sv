// SVA for up_down_counter
// Bind this file to the DUT
bind up_down_counter up_down_counter_sva u_up_down_counter_sva(.*);

module up_down_counter_sva(
  input logic        clk,
  input logic        rst,
  input logic        load,
  input logic        up_down,
  input logic [2:0]  data_in,
  input logic [2:0]  count
);

  // Past-valid guard for $past usage
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Basic sanitation
  assert property (!$isunknown({rst,load,up_down,data_in}))) else $error("Inputs contain X/Z");
  assert property (!$isunknown(count))) else $error("count contains X/Z");

  // Reset behavior (synchronous, highest priority)
  assert property (rst |=> count == 3'd0) else $error("Reset did not drive count to 0");

  // Load behavior (next priority)
  assert property (!rst && load |=> count == $past(data_in))
    else $error("Load did not transfer data_in to count");

  // Count up when not rst/load and up_down=1
  assert property (!rst && !load && up_down
                   |=> count == (($past(count) + 3'd1) & 3'h7))
    else $error("Up-count mismatch");

  // Count down when not rst/load and up_down=0
  assert property (!rst && !load && !up_down
                   |=> count == (($past(count) - 3'd1) & 3'h7))
    else $error("Down-count mismatch");

  // Must move every cycle when not rst/load
  assert property (!rst && !load |=> count != $past(count))
    else $error("count did not change when expected");

  // Held reset keeps count at 0
  assert property ($past(rst) && rst |-> count == 3'd0)
    else $error("count not 0 while reset held");

  // Coverage: exercise key behaviors and wraps
  cover property (rst);                                     // see a reset
  cover property (!rst && load);                            // see a load
  cover property (!rst && !load && up_down [*3]);           // run up for a few cycles
  cover property (!rst && !load && !up_down [*3]);          // run down for a few cycles
  cover property (!rst && !load && up_down  && $past(count)==3'd7 |=> count==3'd0); // wrap up 7->0
  cover property (!rst && !load && !up_down && $past(count)==3'd0 |=> count==3'd7); // wrap down 0->7
  cover property (!rst && load && up_down);                 // load overrides up_down

endmodule