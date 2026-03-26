module mux_1bit_sva (
    input logic clk,
    input logic ctrl,
    input logic D0,
    input logic D1,
    input logic S
);

    // When ctrl is low, the output must pass D0.
    check_select_d0: assert property (
        @(posedge clk) disable iff (1'b0)
        (ctrl == 1'b0) |-> (S == D0)
    );

    // When ctrl is high, the output must pass D1.
    check_select_d1: assert property (
        @(posedge clk) disable iff (1'b0)
        (ctrl == 1'b1) |-> (S == D1)
    );

    // The output must always match the mux select expression.
    check_mux_function: assert property (
        @(posedge clk) disable iff (1'b0)
        S == (ctrl ? D1 : D0)
    );

endmodule