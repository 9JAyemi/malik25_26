module Multiplexer_AC__parameterized36_sva (
    input logic clk,
    input logic [1:0] ctrl,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] D2,
    input logic [0:0] D3,
    input logic [0:0] S
);

    // Combinational DUT sampled on an external clock.
    // No reset is present in the RTL.

    // ctrl=00 selects D0 onto S.
    check_select_d0: assert property (
        @(posedge clk) (ctrl == 2'b00) |-> (S == D0)
    );

    // ctrl=01 selects D1 onto S.
    check_select_d1: assert property (
        @(posedge clk) (ctrl == 2'b01) |-> (S == D1)
    );

    // ctrl=10 selects D2 onto S.
    check_select_d2: assert property (
        @(posedge clk) (ctrl == 2'b10) |-> (S == D2)
    );

    // ctrl=11 selects D3 onto S.
    check_select_d3: assert property (
        @(posedge clk) (ctrl == 2'b11) |-> (S == D3)
    );

endmodule