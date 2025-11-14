// SVA for sync_reset
// Bind module (no ports; names resolve in bound instance’s scope)
module sync_reset_sva #(parameter int N = 2) ();

  // Parameter sanity
  initial begin
    assert (N >= 2) else $fatal(1, "sync_reset: N must be >= 2");
  end

  // Default clock
  default clocking cb @(posedge clk); endclocking

  // Basic invariants
  // Out always equals MSB of shift register
  assert property (out == sync_reg[N-1]);

  // While rst is high, out must be 1
  assert property (rst |-> out);

  // While rst is high, the whole shift register is all 1's
  assert property (rst |-> (sync_reg == {N{1'b1}}));

  // Asynchronous assertion on rst edge takes effect immediately
  assert property (@(posedge rst) out && (sync_reg == {N{1'b1}}));

  // Shift behavior when rst is low: inject 0 into LSB each clk
  assert property (disable iff (rst)
                   sync_reg == { $past(sync_reg)[N-2:0], 1'b0 });

  // Deassertion latency: after rst falls, out stays 1 for exactly N clocks, then 0
  assert property ($fell(rst) |-> (out[*N] ##1 !out));

  // Once out is 0 with rst low, it stays 0 until next rst rise
  assert property ((!rst && !out) |=> (!out until_with $rose(rst)));

  // ------------- Coverage -------------
  // Observe a full reset pulse and synchronous deassertion after N cycles
  cover property ($rose(rst) ##[1:$] $fell(rst) ##1 out[*N] ##1 !out);

  // Multiple back-to-back reset pulses
  cover property ($rose(rst) ##[1:10] $fell(rst) ##[1:10] $rose(rst));

endmodule

// Bind to DUT
bind sync_reset sync_reset_sva #(.N(N)) sync_reset_sva_i();