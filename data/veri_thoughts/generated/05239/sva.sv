module complement_buffer_sva (
    input logic clk,
    input logic Y,
    input logic A
);

    // Y must always be the bitwise complement of A.
    check_output_is_complement: assert property (
        @(posedge clk) Y == ~A
    );

    // A low input must drive Y high.
    check_low_input_drives_high_output: assert property (
        @(posedge clk) !A |-> Y
    );

    // A high input must drive Y low.
    check_high_input_drives_low_output: assert property (
        @(posedge clk) A |-> !Y
    );

endmodule