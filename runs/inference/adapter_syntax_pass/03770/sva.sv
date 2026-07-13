module final_module_sva (
    input logic clk,
    input logic [15:0] in,
    input logic [15:0] out,
    input logic [7:0] out1,
    input logic [7:0] out2
);

    // out1 is the low byte of in.
    check_out1_matches_input_low_byte: assert property (
        @(posedge clk) out1 == in[7:0]
    );

    // out2 is the high byte of in.
    check_out2_matches_input_high_byte: assert property (
        @(posedge clk) out2 == in[15:8]
    );

    // out is the concatenation of out1, out2, and out[0].
    check_out_matches_concatenation: assert property (
        @(posedge clk) out == {out1, out2, out[0]}
    );

    // out[15:8] is the high byte of in.
    check_out_upper_byte_matches_input_high_byte: assert property (
        @(posedge clk) out[15:8] == in[15:8]
    );

    // out[7:0] is the low byte of in.
    check_out_lower_byte_matches_input_low_byte: assert property (
        @(posedge clk) out[7:0] == in[7:0]
    );

    // out[15:8] is a copy of out2.
    check_out_upper_byte_matches_out2: assert property (
        @(posedge clk) out[15:8] == out2
    );

    // out[7:0] is a copy of out1.
    check_out_lower_byte_matches_out1: assert property (
        @(posedge clk) out[7:0] == out1
    );

    // out[15:8] is a copy of in[15:8].
    check_out_upper_byte_matches_input_high_byte: assert property (
        @(posedge clk) out[15:8] == in[15:8]
    );

    // out[7:0] is a copy of in[7:0].
    check_out_lower_byte_matches_input_low_byte: assert property (
        @(posedge clk) out[7:0] == in[7:0]
    );

endmodule