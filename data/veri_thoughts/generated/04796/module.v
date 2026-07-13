
module complement (
    input  [3:0] A,
    output [3:0] Y
);

    // Local signals
    wire [3:0] not_A;

    // Instantiate a 4-bit NOT gate
    not not_A_0 (not_A[0], A[0]); // Instantiate a single-bit NOT gate for each bit
    not not_A_1 (not_A[1], A[1]);
    not not_A_2 (not_A[2], A[2]);
    not not_A_3 (not_A[3], A[3]);

    // Output the complement
    assign Y = not_A;

endmodule
