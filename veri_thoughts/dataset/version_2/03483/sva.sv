module bitwise_complement_sva (
    input  logic       clk,
    input  logic [3:0] a,
    input  logic [3:0] out
);

    // The output vector always equals the bitwise complement of the input vector.
    check_vector_complement: assert property (
        @(posedge clk) out == ~a
    );

    // Output bit 0 always matches the complement of input bit 0.
    check_bit0_complement: assert property (
        @(posedge clk) out[0] == ~a[0]
    );

    // Output bit 1 always matches the complement of input bit 1.
    check_bit1_complement: assert property (
        @(posedge clk) out[1] == ~a[1]
    );

    // Output bit 2 always matches the complement of input bit 2.
    check_bit2_complement: assert property (
        @(posedge clk) out[2] == ~a[2]
    );

    // Output bit 3 always matches the complement of input bit 3.
    check_bit3_complement: assert property (
        @(posedge clk) out[3] == ~a[3]
    );

endmodule