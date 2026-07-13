module mux_4to1_case_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic [1:0] sel,
    input logic Y
);

    // sel=00 routes A to Y.
    check_sel_00_routes_a: assert property (
        @($global_clock) (sel == 2'b00) |-> (Y == A)
    );

    // sel=01 routes B to Y.
    check_sel_01_routes_b: assert property (
        @($global_clock) (sel == 2'b01) |-> (Y == B)
    );

    // sel=10 routes C to Y.
    check_sel_10_routes_c: assert property (
        @($global_clock) (sel == 2'b10) |-> (Y == C)
    );

    // sel=11 routes D to Y.
    check_sel_11_routes_d: assert property (
        @($global_clock) (sel == 2'b11) |-> (Y == D)
    );

endmodule