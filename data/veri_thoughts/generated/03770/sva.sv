module final_module_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [15:0] out
);

    // Truncation of the 17-bit concatenation maps in[6:0] onto out[15:9].
    check_truncated_concat_upper_slice: assert property (
        @(posedge clk) out[15:9] == in[6:0]
    );

    // The upper input byte maps directly onto out[8:1].
    check_upper_input_byte_to_out_8_to_1: assert property (
        @(posedge clk) out[8:1] == in[15:8]
    );

    // A high AND term on in[7] and in[8] is captured into out[0] on the next clock.
    check_out0_sets_from_and_term: assert property (
        @(posedge clk) (in[7] & in[8]) |=> out[0]
    );

    // A low AND term on in[7] and in[8] is captured into out[0] on the next clock.
    check_out0_clears_from_and_term: assert property (
        @(posedge clk) !(in[7] & in[8]) |=> !out[0]
    );

endmodule