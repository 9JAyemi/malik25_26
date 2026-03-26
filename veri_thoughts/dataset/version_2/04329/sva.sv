module add_sub_4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic M,
    input logic [3:0] S
);

    wire [3:0] B_inv;
    wire [3:0] C_in;
    wire [3:0] S_add;
    wire [3:0] S_sub;

    assign B_inv = ~B;
    assign C_in  = M ? B_inv : 4'b0000;
    assign S_add = A + B;
    assign S_sub = A + B_inv + C_in;

    // Output always matches the selected datapath result.
    check_output_matches_selected_result: assert property (
        @(posedge clk) S == (M ? S_sub : S_add)
    );

    // In add mode, output is the 4-bit sum of A and B.
    check_add_mode_sum: assert property (
        @(posedge clk) !M |-> (S == S_add)
    );

    // In M=1 mode, output follows the implemented A + ~B + C_in path.
    check_mode_one_sum: assert property (
        @(posedge clk) M |-> (S == S_sub)
    );

    // In add mode with B at zero, output passes A through.
    check_add_mode_b_zero_passthrough: assert property (
        @(posedge clk) (!M && (B == 4'b0000)) |-> (S == A)
    );

    // In add mode with A at zero, output passes B through.
    check_add_mode_a_zero_passthrough: assert property (
        @(posedge clk) (!M && (A == 4'b0000)) |-> (S == B)
    );

    // In M=1 mode with B all ones, both inverted-B terms are zero.
    check_mode_one_all_ones_b_passthrough: assert property (
        @(posedge clk) (M && (B == 4'hF)) |-> (S == A)
    );

    // In add mode, the LSB is the XOR of the input LSBs.
    check_add_mode_lsb_xor: assert property (
        @(posedge clk) !M |-> (S[0] == (A[0] ^ B[0]))
    );

    // In M=1 mode, the LSB reduces to A[0].
    check_mode_one_lsb_tracks_a: assert property (
        @(posedge clk) M |-> (S[0] == A[0])
    );

    // Stable inputs keep the combinational output stable.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(M)) |-> $stable(S)
    );

endmodule