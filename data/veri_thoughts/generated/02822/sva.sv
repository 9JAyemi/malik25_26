module multiplexer_sva #(
    parameter int N = 8,
    parameter int M = 2
)(
    input logic clk,                 // Checker sampling clock (DUT has no clock/reset)
    input logic [N-1:0] A,
    input logic [N-1:0] B,
    input logic [N-1:0] C,
    input logic [M-1:0] S,
    input logic [N-1:0] Y
);
    // Analysis: DUT has no clock/reset; purely combinational mux; Y selects A/B/C by S, else 0.

    // Y implements the mux function exactly (A for 00, B for 01, C for 10, else 0).
    check_mux_function: assert property (
        @(posedge clk)
            Y == ((S == 2'b00) ? A :
                  (S == 2'b01) ? B :
                  (S == 2'b10) ? C : '0)
    );

    // When S==00 (zero-extended), Y equals A.
    check_select_A_when_S_00: assert property (
        @(posedge clk) (S == 2'b00) |-> (Y == A)
    );

    // When S==01 (zero-extended), Y equals B.
    check_select_B_when_S_01: assert property (
        @(posedge clk) (S == 2'b01) |-> (Y == B)
    );

    // When S==10 (zero-extended), Y equals C.
    check_select_C_when_S_10: assert property (
        @(posedge clk) (S == 2'b10) |-> (Y == C)
    );

    // When S is not 00/01/10, Y drives all zeros (default case).
    check_default_zero_when_other_S: assert property (
        @(posedge clk) (!( (S == 2'b00) || (S == 2'b01) || (S == 2'b10) )) |-> (Y == '0)
    );

    // If A,B,C,S are stable cycle-to-cycle, Y must remain stable (purely combinational).
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({A,B,C,S}) |-> $stable(Y)
    );

    // For M>2, any nonzero upper bits in S force the default case (Y==0).
    generate
        if (M > 2) begin : gen_hi_default_zero
            check_upper_bits_force_default_zero: assert property (
                @(posedge clk) (S[M-1:2] != '0) |-> (Y == '0)
            );
        end
    endgenerate
endmodule