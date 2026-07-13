module mux_4to1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic [1:0] SEL,
    input logic Y
);

    // SEL=00 routes A to Y.
    check_sel_00_routes_a: assert property (
        @(posedge clk) (SEL == 2'b00) |-> (Y == A)
    );

    // SEL=01 routes B to Y.
    check_sel_01_routes_b: assert property (
        @(posedge clk) (SEL == 2'b01) |-> (Y == B)
    );

    // SEL=10 routes C to Y.
    check_sel_10_routes_c: assert property (
        @(posedge clk) (SEL == 2'b10) |-> (Y == C)
    );

    // SEL=11 routes D to Y.
    check_sel_11_routes_d: assert property (
        @(posedge clk) (SEL == 2'b11) |-> (Y == D)
    );

endmodule