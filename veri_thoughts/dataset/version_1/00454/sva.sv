// SVA for reg32_async_reset_load
// Bind this file to the DUT for checks and coverage

module reg32_async_reset_load_sva (
  input clk,
  input reset,
  input load,
  input [31:0] data_in,
  input [31:0] data_out
);

  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset drives 0 immediately
  property p_async_reset_immediate;
    @(negedge reset) data_out == 32'h0;
  endproperty
  assert property (p_async_reset_immediate);

  // While in reset, next sampled value is 0 (covers posedge clk during reset)
  assert property (@(posedge clk) !reset |=> data_out == 32'h0);

  // Reset dominates load at clock edge
  assert property (@(posedge clk) (!reset && load) |=> data_out == 32'h0);

  // Synchronous load capture when out of reset
  assert property (@(posedge clk) disable iff (!reset)
                   load |=> data_out == $past(data_in));

  // Hold when no load and out of reset
  assert property (@(posedge clk) disable iff (!reset)
                   !load |=> data_out == $past(data_out));

  // Output is known when out of reset
  assert property (@(posedge clk) reset |-> !$isunknown(data_out));

  // Inputs are known at sampling
  assert property (@(posedge clk) !$isunknown({reset,load}));

  // On reset release, first sampled value remains 0
  assert property (@(posedge clk) $rose(reset) |-> data_out == 32'h0);

  // Coverage
  cover property (@(negedge reset) 1);                                  // reset asserted
  cover property (@(posedge clk) !reset ##1 reset);                      // reset release
  cover property (@(posedge clk) disable iff (!reset) load);             // a write
  cover property (@(posedge clk) disable iff (!reset) load ##1 load);    // back-to-back writes
  cover property (@(posedge clk) disable iff (!reset) !load [*2]);       // hold for 2+ cycles
  cover property (@(posedge clk) disable iff (!reset)
                  load && data_in == 32'hFFFF_FFFF);                     // write max
  cover property (@(posedge clk) disable iff (!reset)
                  load && data_in == 32'hA5A5_A5A5);                     // write pattern

endmodule

bind reg32_async_reset_load reg32_async_reset_load_sva sva_inst (.*);