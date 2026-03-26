module mux_sva #
  (
    parameter WIDTH = 1
  )
  (
    input logic ctrl,
    input logic [WIDTH-1:0] D0,
    input logic [WIDTH-1:0] D1,
    input logic [WIDTH-1:0] S
  );

  // No RTL clock or reset; sample the combinational behavior on the global clock.

  // When ctrl is high, the mux output must be D1.
  check_select_d1: assert property (
    @($global_clock) ctrl |-> (S == D1)
  );

  // When ctrl is low, the mux output must be D0.
  check_select_d0: assert property (
    @($global_clock) !ctrl |-> (S == D0)
  );

  // If both data inputs match, the output must match that common value.
  check_equal_inputs_common_value: assert property (
    @($global_clock) (D0 == D1) |-> (S == D0)
  );

endmodule