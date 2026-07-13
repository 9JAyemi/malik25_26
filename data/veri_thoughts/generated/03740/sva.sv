module mux2to1_sva (
    input logic        clk,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic        S,
    input logic [31:0] Y
);

    // When S is low, the mux output selects A.
    check_select_a: assert property (
        @(posedge clk) (S == 1'b0) |-> (Y == A)
    );

    // When S is high, the mux output selects B.
    check_select_b: assert property (
        @(posedge clk) (S == 1'b1) |-> (Y == B)
    );

    // The output always matches the RTL mux expression.
    check_mux_function: assert property (
        @(posedge clk) Y == ((S == 1'b0) ? A : B)
    );

endmodule