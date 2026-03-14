module mux_2_1_sva (
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);
    // Combinational 2:1 mux; no clock/reset in RTL; sample on any input edge.

    // Functional equation: Y must equal (S ? B : A) at all times.
    check_mux_function: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge S or negedge S)
            Y == (S ? B : A)
    );

    // When S is 0, Y equals A.
    check_select0_path: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge S or negedge S)
            (S == 1'b0) |-> (Y == A)
    );

    // When S is 1, Y equals B.
    check_select1_path: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge S or negedge S)
            (S == 1'b1) |-> (Y == B)
    );
endmodule