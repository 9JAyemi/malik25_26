module binary_adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] S,
    input logic       Cout
);

    // Full 5-bit result matches A + B + Cin.
    check_full_result: assert property (
        @(posedge clk) disable iff (1'b0)
        {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Sum bit 0 matches the full-adder XOR equation.
    check_sum_bit0: assert property (
        @(posedge clk) disable iff (1'b0)
        S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Lower two sum bits match a 2-bit add with carry-in.
    check_lower_two_bits: assert property (
        @(posedge clk) disable iff (1'b0)
        S[1:0] == (A[1:0] + B[1:0] + Cin)
    );

    // Lower three sum bits match a 3-bit add with carry-in.
    check_lower_three_bits: assert property (
        @(posedge clk) disable iff (1'b0)
        S[2:0] == (A[2:0] + B[2:0] + Cin)
    );

    // Adding zero on B with Cin low passes A through.
    check_add_zero_on_b: assert property (
        @(posedge clk) disable iff (1'b0)
        (B == 4'b0000 && Cin == 1'b0) |-> (S == A && Cout == 1'b0)
    );

    // Adding zero on A with Cin low passes B through.
    check_add_zero_on_a: assert property (
        @(posedge clk) disable iff (1'b0)
        (A == 4'b0000 && Cin == 1'b0) |-> (S == B && Cout == 1'b0)
    );

    // All-zero inputs produce an all-zero result.
    check_all_zero_inputs: assert property (
        @(posedge clk) disable iff (1'b0)
        (A == 4'b0000 && B == 4'b0000 && Cin == 1'b0) |-> (S == 4'b0000 && Cout == 1'b0)
    );

    // Carry-in alone produces a value of one.
    check_cin_only: assert property (
        @(posedge clk) disable iff (1'b0)
        (A == 4'b0000 && B == 4'b0000 && Cin == 1'b1) |-> (S == 4'b0001 && Cout == 1'b0)
    );

    // Maximum inputs with carry-in produce 5'h1F.
    check_max_with_cin: assert property (
        @(posedge clk) disable iff (1'b0)
        (A == 4'hF && B == 4'hF && Cin == 1'b1) |-> (S == 4'hF && Cout == 1'b1)
    );

endmodule