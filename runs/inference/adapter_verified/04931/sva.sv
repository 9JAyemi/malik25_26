module mux_4to1_sva (
    input logic clk,
    input logic [1:0] S,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);

// S=00 routes C to Y.
    check_select_00_routes_c: assert property (
        @(posedge clk) (S == 2'b00) |-> (Y == C)
    );

// S=01 routes D to Y.
    check_select_01_routes_d: assert property (
        @(posedge clk) (S == 2'b01) |-> (Y == D)
    );

// S=10 routes A to Y.
    check_select_10_routes_a: assert property (
        @(posedge clk) (S == 2'b10) |-> (Y == A)
    );

// S=11 routes B to Y.
    check_select_11_routes_b: assert property (
        @(posedge clk) (S == 2'b11) |-> (Y == B)
    );

endmodule
