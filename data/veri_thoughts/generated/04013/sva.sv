module adder_sva #(
    parameter WIDTH = 4
) (
    input logic clk,
    input logic [WIDTH-1:0] A,
    input logic [WIDTH-1:0] B,
    input logic Cin,
    input logic [WIDTH-1:0] S,
    input logic Cout
);

    function automatic logic maj3(input logic x, input logic y, input logic z);
        maj3 = (x & y) | (y & z) | (x & z);
    endfunction

    generate
        if (WIDTH == 4) begin : gen_width4_assertions
            // The concatenated outputs must equal the 5-bit addition result.
            check_full_sum_relation: assert property (
                @(posedge clk) disable iff (1'b0)
                {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
            );

            // Sum bit 0 must match the first full-adder XOR.
            check_sum_bit0: assert property (
                @(posedge clk) disable iff (1'b0)
                S[0] == (A[0] ^ B[0] ^ Cin)
            );

            // Sum bit 1 must use the carry from bit 0.
            check_sum_bit1: assert property (
                @(posedge clk) disable iff (1'b0)
                S[1] == (A[1] ^ B[1] ^ maj3(A[0], B[0], Cin))
            );

            // Sum bit 2 must use the carry from bit 1.
            check_sum_bit2: assert property (
                @(posedge clk) disable iff (1'b0)
                S[2] == (A[2] ^ B[2] ^ maj3(A[1], B[1], maj3(A[0], B[0], Cin)))
            );

            // Sum bit 3 must use the carry from bit 2.
            check_sum_bit3: assert property (
                @(posedge clk) disable iff (1'b0)
                S[3] == (A[3] ^ B[3] ^ maj3(A[2], B[2], maj3(A[1], B[1], maj3(A[0], B[0], Cin))))
            );

            // Cout must match the carry out of the final full adder.
            check_cout_chain: assert property (
                @(posedge clk) disable iff (1'b0)
                Cout == maj3(A[3], B[3], maj3(A[2], B[2], maj3(A[1], B[1], maj3(A[0], B[0], Cin))))
            );
        end
    endgenerate

endmodule