module mux4to1_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic S0,
    input logic S1
);

    // Y must implement the full 4:1 mux function.
    check_mux_function: assert property (
        @(posedge clk)
        Y == (((S1 == 1'b0) && (S0 == 1'b0)) ? A :
              ((S1 == 1'b0) && (S0 == 1'b1)) ? B :
              ((S1 == 1'b1) && (S0 == 1'b0)) ? C :
                                               D)
    );

    // When select is 00, Y must equal A.
    check_select_00: assert property (
        @(posedge clk)
        ((S1 == 1'b0) && (S0 == 1'b0)) |-> (Y == A)
    );

    // When select is 01, Y must equal B.
    check_select_01: assert property (
        @(posedge clk)
        ((S1 == 1'b0) && (S0 == 1'b1)) |-> (Y == B)
    );

    // When select is 10, Y must equal C.
    check_select_10: assert property (
        @(posedge clk)
        ((S1 == 1'b1) && (S0 == 1'b0)) |-> (Y == C)
    );

    // When select is 11, Y must equal D.
    check_select_11: assert property (
        @(posedge clk)
        ((S1 == 1'b1) && (S0 == 1'b1)) |-> (Y == D)
    );

endmodule