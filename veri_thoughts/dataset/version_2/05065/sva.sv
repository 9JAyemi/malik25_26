module mux4_2_sva (
    input logic       clk,
    input logic       A,
    input logic       B,
    input logic       C,
    input logic       D,
    input logic [1:0] S,
    input logic       Y
);

    // S=00 selects input A.
    check_select_a: assert property (
        @(posedge clk) (S == 2'b00) |-> (Y == A)
    );

    // S=01 selects input B.
    check_select_b: assert property (
        @(posedge clk) (S == 2'b01) |-> (Y == B)
    );

    // S=10 selects input C.
    check_select_c: assert property (
        @(posedge clk) (S == 2'b10) |-> (Y == C)
    );

    // S=11 selects input D.
    check_select_d: assert property (
        @(posedge clk) (S == 2'b11) |-> (Y == D)
    );

endmodule