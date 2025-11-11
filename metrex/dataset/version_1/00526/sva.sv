// SVA for module: register
module register_sva #(parameter WIDTH = 8, parameter RESET_VALUE = 0)
(
  input  logic [WIDTH-1:0] DataIn,
  input  logic             Write,
  input  logic             Clk,
  input  logic             Reset,
  input  logic             SyncReset,
  input  logic [WIDTH-1:0] DataOut
);

  default clocking cb @(posedge Clk); endclocking

  // Track if we've seen any reset edge to enable post-reset X checks
  bit seen_async_reset;
  initial seen_async_reset = 1'b0;
  always @(posedge Reset or posedge SyncReset) seen_async_reset <= 1'b1;

  // Asynchronous reset effects must be immediate within the same time slot
  ap_async_reset_immediate:    assert property (@(posedge Reset)      ##0 (DataOut == RESET_VALUE));
  ap_async_syncreset_immediate:assert property (@(posedge SyncReset)  ##0 (DataOut == RESET_VALUE));

  // On a clock edge with reset asserted, output must be reset value on next cycle
  ap_clk_when_reset_holds:     assert property ( (Reset || SyncReset) |=> (DataOut == RESET_VALUE) );

  // Normal write and hold behavior when not in reset
  ap_write_updates:            assert property ( disable iff (Reset || SyncReset)
                                                 Write |=> (DataOut == $past(DataIn)) );

  ap_no_write_holds:           assert property ( disable iff (Reset || SyncReset)
                                                 !Write |=> (DataOut == $past(DataOut)) );

  // Write cannot override reset
  ap_write_blocked_by_reset:   assert property ( (Reset || SyncReset) && Write |=> (DataOut == RESET_VALUE) );

  // After any reset has been observed, DataOut should never be X/Z on active cycles
  ap_no_unknown_after_reset:   assert property ( seen_async_reset |-> !$isunknown(DataOut) );

  // ------------------------------------------------------------
  // Coverage (concise, exercises key behaviors)
  // ------------------------------------------------------------
  cp_async_reset:              cover property (@(posedge Reset)      ##0 (DataOut == RESET_VALUE));
  cp_async_syncreset:          cover property (@(posedge SyncReset)  ##0 (DataOut == RESET_VALUE));

  cp_write_update:             cover property ( disable iff (Reset || SyncReset)
                                                Write ##1 (DataOut == $past(DataIn)) );

  cp_hold_no_write:            cover property ( disable iff (Reset || SyncReset)
                                                !Write ##1 (DataOut == $past(DataOut)) );

  cp_b2b_writes:               cover property ( disable iff (Reset || SyncReset)
                                                Write ##1 Write ##1 Write );

  localparam logic [WIDTH-1:0] ALL0 = '0;
  localparam logic [WIDTH-1:0] ALL1 = {WIDTH{1'b1}};
  cp_write_zero:               cover property ( disable iff (Reset || SyncReset)
                                                (Write && DataIn == ALL0) ##1 (DataOut == ALL0) );
  cp_write_ones:               cover property ( disable iff (Reset || SyncReset)
                                                (Write && DataIn == ALL1) ##1 (DataOut == ALL1) );

  cp_both_resets_high:         cover property (Reset && SyncReset);

endmodule

// Bind example:
// bind register register_sva #(.WIDTH(WIDTH), .RESET_VALUE(RESET_VALUE)) reg_sva
// (.*);