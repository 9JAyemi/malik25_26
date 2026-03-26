module four_bit_adder_assertions (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    // Combined output matches 4-bit addition with carry-in.
    check_total_addition: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Sum bit 0 matches the first full-adder stage.
    check_sum_bit0_logic: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Sum bit 1 matches addition of the low two input bits.
    check_sum_bit1_logic: assert property (
        @(posedge clk) S[1] == (({1'b0, A[1:0]} + {1'b0, B[1:0]} + Cin)[1])
    );

    // Sum bit 2 matches addition of the low three input bits.
    check_sum_bit2_logic: assert property (
        @(posedge clk) S[2] == (({1'b0, A[2:0]} + {1'b0, B[2:0]} + Cin)[2])
    );

    // Sum bit 3 matches addition of all four input bits.
    check_sum_bit3_logic: assert property (
        @(posedge clk) S[3] == (({1'b0, A} + {1'b0, B} + Cin)[3])
    );

    // Carry-out matches the fifth bit of the full addition.
    check_cout_logic: assert property (
        @(posedge clk) Cout == (({1'b0, A} + {1'b0, B} + Cin)[4])
    );

endmodule