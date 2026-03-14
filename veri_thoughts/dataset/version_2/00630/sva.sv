module Multiplexer_AC__parameterized50_sva #(
    parameter WIDTH = 1
) (
    input logic clk,
    input logic ctrl,
    input logic [WIDTH-1:0] D0,
    input logic [WIDTH-1:0] D1,
    input logic [WIDTH-1:0] S
);
    // Output equals the RTL ternary expression each cycle.
    check_mux_equation: assert property (
        @(posedge clk) S === ((ctrl == 1'b0) ? D0 : D1)
    );

    // When ctrl is 0, S equals D0.
    check_ctrl0_routes_D0: assert property (
        @(posedge clk) (ctrl === 1'b0) |-> (S === D0)
    );

    // When ctrl is 1, S equals D1.
    check_ctrl1_routes_D1: assert property (
        @(posedge clk) (ctrl === 1'b1) |-> (S === D1)
    );

    // If D0 and D1 are equal (including X/Z), S equals that value.
    check_equal_inputs_propagate: assert property (
        @(posedge clk) (D0 === D1) |-> (S === D0)
    );

    // With ctrl=0 and D0 known, S has no X/Z.
    check_no_unknown_when_ctrl0: assert property (
        @(posedge clk) (ctrl === 1'b0 && !$isunknown(D0)) |-> !$isunknown(S)
    );

    // With ctrl=1 and D1 known, S has no X/Z.
    check_no_unknown_when_ctrl1: assert property (
        @(posedge clk) (ctrl === 1'b1 && !$isunknown(D1)) |-> !$isunknown(S)
    );
endmodule