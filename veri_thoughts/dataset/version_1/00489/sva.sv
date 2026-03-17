module rippleCarryAdder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] Sum,
    input logic Cout,
    input logic [3:0] C,
    input logic [3:0] S
);

    // Sum must mirror the internal S bus.
    check_sum_alias: assert property (
        @(posedge clk) Sum == S
    );

    // FA0 sum must match the full-adder XOR equation.
    check_fa0_sum_function: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // FA0 carry must match the full-adder carry equation.
    check_fa0_carry_function: assert property (
        @(posedge clk) C[0] == ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))
    );

    // FA1 sum must use C[0] as its carry-in.
    check_fa1_sum_function: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ C[0])
    );

    // FA1 carry must match the full-adder carry equation.
    check_fa1_carry_function: assert property (
        @(posedge clk) C[1] == ((A[1] & B[1]) | (A[1] & C[0]) | (B[1] & C[0]))
    );

    // FA2 sum must use C[1] as its carry-in.
    check_fa2_sum_function: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ C[1])
    );

    // FA2 carry must match the full-adder carry equation.
    check_fa2_carry_function: assert property (
        @(posedge clk) C[2] == ((A[2] & B[2]) | (A[2] & C[1]) | (B[2] & C[1]))
    );

    // FA3 sum must use C[2] as its carry-in.
    check_fa3_sum_function: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ C[2])
    );

    // FA3 carry-out must match the full-adder carry equation.
    check_fa3_carry_function: assert property (
        @(posedge clk) Cout == ((A[3] & B[3]) | (A[3] & C[2]) | (B[3] & C[2]))
    );

    // The full 5-bit result must equal A + B + Cin.
    check_overall_addition_result: assert property (
        @(posedge clk) {Cout, Sum} == ({1'b0, A} + {1'b0, B} + {{4{1'b0}}, Cin})
    );

endmodule