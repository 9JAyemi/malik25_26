module four_bit_adder_assertions (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] Sum,
    input logic Cout
);

    // Sum[0] is the XOR of A[0], B[0], and Cin.
    check_sum_bit0_definition: assert property (
        @(posedge clk) disable iff (1'b0)
        Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Sum[1] uses Sum[0] as the third XOR input.
    check_sum_bit1_definition: assert property (
        @(posedge clk) disable iff (1'b0)
        Sum[1] == (A[1] ^ B[1] ^ Sum[0])
    );

    // Sum[2] uses Sum[1] as the third XOR input.
    check_sum_bit2_definition: assert property (
        @(posedge clk) disable iff (1'b0)
        Sum[2] == (A[2] ^ B[2] ^ Sum[1])
    );

    // Sum[3] uses Sum[2] as the third XOR input.
    check_sum_bit3_definition: assert property (
        @(posedge clk) disable iff (1'b0)
        Sum[3] == (A[3] ^ B[3] ^ Sum[2])
    );

    // Sum matches the expanded XOR chain from the inputs.
    check_sum_bus_definition: assert property (
        @(posedge clk) disable iff (1'b0)
        Sum == {
            (A[3] ^ B[3] ^ A[2] ^ B[2] ^ A[1] ^ B[1] ^ A[0] ^ B[0] ^ Cin),
            (A[2] ^ B[2] ^ A[1] ^ B[1] ^ A[0] ^ B[0] ^ Cin),
            (A[1] ^ B[1] ^ A[0] ^ B[0] ^ Cin),
            (A[0] ^ B[0] ^ Cin)
        }
    );

    // Cout is tied directly to Sum[3].
    check_cout_matches_sum_msb: assert property (
        @(posedge clk) disable iff (1'b0)
        Cout == Sum[3]
    );

    // Cout matches the expanded XOR expression for the top bit.
    check_cout_definition: assert property (
        @(posedge clk) disable iff (1'b0)
        Cout == (A[3] ^ B[3] ^ A[2] ^ B[2] ^ A[1] ^ B[1] ^ A[0] ^ B[0] ^ Cin)
    );

endmodule