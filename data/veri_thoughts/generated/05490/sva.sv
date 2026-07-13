module adder_4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    // Checks the adder output matches A + B + Cin.
    check_total_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + {4'b0000, Cin})
    );

    // Checks bit 0 sum implements the full-adder XOR.
    check_sum_bit0: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Checks bit 1 sum uses the carry from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
    );

    // Checks carry-out matches overflow of the 4-bit addition.
    check_cout_overflow: assert property (
        @(posedge clk) Cout == (({1'b0, A} + {1'b0, B} + {4'b0000, Cin}) > 5'd15)
    );

    // Checks adding zero to A passes A through.
    check_identity_a: assert property (
        @(posedge clk) ((B == 4'b0000) && (Cin == 1'b0)) |-> ((S == A) && (Cout == 1'b0))
    );

    // Checks adding zero to B passes B through.
    check_identity_b: assert property (
        @(posedge clk) ((A == 4'b0000) && (Cin == 1'b0)) |-> ((S == B) && (Cout == 1'b0))
    );

    // Checks Cin alone increments zero to one.
    check_cin_only: assert property (
        @(posedge clk) ((A == 4'b0000) && (B == 4'b0000) && (Cin == 1'b1)) |-> ((S == 4'b0001) && (Cout == 1'b0))
    );

    // Checks incrementing 4'hF produces wraparound with carry.
    check_increment_overflow: assert property (
        @(posedge clk) ((A == 4'b1111) && (B == 4'b0000) && (Cin == 1'b1)) |-> ((S == 4'b0000) && (Cout == 1'b1))
    );

endmodule