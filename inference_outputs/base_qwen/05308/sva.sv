module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] sum
);

    // Combinational logic, so use @(posedge clk)
    // Full adder logic for each bit is combinational, but we clock the assertions

    // Least significant bit
    // Sum is correct for A[0] + B[0] + 0
    least_significant_bit: assert property (
        @(posedge clk) $rose(A[0]) |-> (sum[0] == A[0] ^ B[0])
    );

    // Second least significant bit
    // Sum is correct for A[1] + B[1] + carry from least significant bit
    second_least_significant_bit: assert property (
        @(posedge clk) $rose(A[1]) |-> (sum[1] == A[1] ^ B[1] ^ sum[0])
    );

    // Third least significant bit
    // Sum is correct for A[2] + B[2] + carry from second least significant bit
    third_least_significant_bit: assert property (
        @(posedge clk) $rose(A[2]) |-> (sum[2] == A[2] ^ B[2] ^ sum[1])
    );

    // Most significant bit
    // Sum is correct for A[3] + B[3] + carry from third least significant bit
    most_significant_bit: assert property (
        @(posedge clk) $rose(A[3]) |-> (sum[3] == A[3] ^ B[3] ^ sum[2])
    );

endmodule