module my_mux_sva (
    input logic clk,
    input logic A0,
    input logic A1,
    input logic S,
    input logic X
);

    // When S is exactly 0, X must follow A0.
    check_select_low_routes_a0: assert property (
        @(posedge clk) (S === 1'b0) |-> (X === A0)
    );

    // When S is not exactly 0, X must follow A1.
    check_select_not_low_routes_a1: assert property (
        @(posedge clk) (S !== 1'b0) |-> (X === A1)
    );

endmodule