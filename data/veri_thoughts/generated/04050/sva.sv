module weak_not_sva (
    input logic clk,
    input logic Z,
    input logic Y
);

    // Y must always be the bitwise inverse of Z.
    check_output_is_bitwise_inverse: assert property (
        @(posedge clk) (Y === ~Z)
    );

    // A high Z must produce a low Y.
    check_high_input_drives_low_output: assert property (
        @(posedge clk) (Z === 1'b1) |-> (Y === 1'b0)
    );

    // A low Z must produce a high Y.
    check_low_input_drives_high_output: assert property (
        @(posedge clk) (Z === 1'b0) |-> (Y === 1'b1)
    );

endmodule