module top_module_sva (
    input logic clk,
    input logic rst_n,
    input logic [3:0] in_vec,
    input logic [7:0] out_vec,
    input logic msb_out,
    input logic mid_out,
    input logic lsb_out,
    input logic [7:0] jc_out,
    input logic [3:0] bn_out,
    input logic [7:0] state
);

    // A sampled low reset leaves the counter state cleared on the next clock.
    check_reset_clears_state: assert property (
        @(posedge clk) !rst_n |=> (state == 8'b00000000)
    );

    // A sampled low reset leaves the decoded counter output cleared on the next clock.
    check_reset_clears_jc_out: assert property (
        @(posedge clk) !rst_n |=> (jc_out == 8'b00000000)
    );

    // The listed decode states pass through unchanged to jc_out.
    check_jc_decode_known_states: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state inside {8'b00000000, 8'b10000000, 8'b11000000, 8'b11100000,
                       8'b11110000, 8'b01111000, 8'b00111100, 8'b00011110,
                       8'b00001111}) |-> (jc_out == state)
    );

    // Any unlisted decode state drives jc_out to zero.
    check_jc_decode_default_zero: assert property (
        @(posedge clk) disable iff (!rst_n)
        !(state inside {8'b00000000, 8'b10000000, 8'b11000000, 8'b11100000,
                        8'b11110000, 8'b01111000, 8'b00111100, 8'b00011110,
                        8'b00001111}) |-> (jc_out == 8'b00000000)
    );

    // Once the counter state is zero, it stays zero on later clocks.
    check_zero_state_sticky: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == 8'b00000000) |=> (state == 8'b00000000)
    );

    // The binary-number block copies in_vec directly to bn_out.
    check_binary_vector_copy: assert property (
        @(posedge clk) disable iff (!rst_n)
        (bn_out == in_vec)
    );

    // The top MSB output reflects bit 3 of in_vec.
    check_msb_output_matches_input: assert property (
        @(posedge clk) disable iff (!rst_n)
        (msb_out == in_vec[3])
    );

    // The top MID output reflects bit 2 of in_vec.
    check_mid_output_matches_input: assert property (
        @(posedge clk) disable iff (!rst_n)
        (mid_out == in_vec[2])
    );

    // The top LSB output reflects bit 1 of in_vec.
    check_lsb_output_matches_input: assert property (
        @(posedge clk) disable iff (!rst_n)
        (lsb_out == in_vec[1])
    );

    // The functional block ORs jc_out with the zero-extended binary vector.
    check_functional_or_result: assert property (
        @(posedge clk) disable iff (!rst_n)
        (out_vec == (jc_out | {4'b0000, bn_out}))
    );

    // When the counter state is zero, out_vec is just in_vec in the low nibble.
    check_zero_state_top_output: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == 8'b00000000) |-> (out_vec == {4'b0000, in_vec})
    );

    // A sampled low reset leaves out_vec equal to the low-nibble input on the next clock.
    check_reset_top_output: assert property (
        @(posedge clk) !rst_n |=> (out_vec == {4'b0000, in_vec})
    );

endmodule