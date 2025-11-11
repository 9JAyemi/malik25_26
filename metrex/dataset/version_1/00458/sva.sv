// SVA for and_async_reset
// Bind this file to the DUT to check/cover behavior

module and_async_reset_sva (
  input logic a,
  input logic b,
  input logic reset,   // active-low reset_n? Here: reset==0 => asserted
  input logic out
);

  // Sample on any relevant edge; use ##0 to check after NBA updates
  default clocking cb @(
    posedge a or negedge a or
    posedge b or negedge b or
    posedge reset or negedge reset
  ); endclocking

  // Basic sanity: known values
  ap_reset_known:  assert property (!$isunknown(reset)) else $error("reset X/Z");
  ap_out_known:    assert property (!$isunknown(out))   else $error("out X/Z");
  ap_in_known_en:  assert property (reset |-> !$isunknown({a,b}))
                   else $error("a/b X/Z while enabled (reset=1)");

  // Functional equivalence (combinational, zero-latency in delta)
  ap_func: assert property (1'b1 |-> ##0 (out == (reset ? (a & b) : 1'b0)))
           else $error("Functional mismatch: out vs (reset ? a&b : 0)");

  // Asynchronous reset behavior on edges
  ap_rst_assert:   assert property ($fell(reset) |-> ##0 (out == 1'b0))
                   else $error("Out not cleared on reset assert (reset->0)");
  ap_rst_deassert: assert property ($rose(reset) |-> ##0 (out == (a & b)))
                   else $error("Out not updated on reset deassert (reset->1)");

  // Coverage
  cp_rst_fall:  cover property ($fell(reset));
  cp_rst_rise:  cover property ($rose(reset));

  cp_and_00: cover property (reset && !a && !b ##0 (out == 1'b0));
  cp_and_01: cover property (reset && !a &&  b ##0 (out == 1'b0));
  cp_and_10: cover property (reset &&  a && !b ##0 (out == 1'b0));
  cp_and_11: cover property (reset &&  a &&  b ##0 (out == 1'b1));

endmodule

// Bind into the DUT
bind and_async_reset and_async_reset_sva sva_i (
  .a(a), .b(b), .reset(reset), .out(out)
);