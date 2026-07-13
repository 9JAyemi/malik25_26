module mux2to1_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);
    // Y must equal the selected input per S
    check_mux_function: assert property (
        @(posedge CLK) Y == ((S == 1'b0) ? A : B)
    );

    // If inputs are equal, Y must equal that value regardless of S
    check_equal_inputs: assert property (
        @(posedge CLK) (A == B) |-> (Y == A)
    );

    // If A and B differ and Y equals A, S must be 0
    check_inverse_select_A: assert property (
        @(posedge CLK) ((A != B) && (Y == A)) |-> (S == 1'b0)
    );

    // If A and B differ and Y equals B, S must be 1
    check_inverse_select_B: assert property (
        @(posedge CLK) ((A != B) && (Y == B)) |-> (S == 1'b1)
    );
endmodule