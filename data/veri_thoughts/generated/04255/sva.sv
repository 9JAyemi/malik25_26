module gray_code_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] bin_in,
    input logic [3:0] gray_out
);

    // Reset clears the registered output on the next clock.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |=> (gray_out == 4'b0000)
    );

    // Gray output matches the previous cycle's binary input encoding.
    check_gray_vector_encoding: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (gray_out == {
            $past(bin_in[3]),
            ($past(bin_in[3]) ^ $past(bin_in[2])),
            ($past(bin_in[2]) ^ $past(bin_in[1])),
            ($past(bin_in[1]) ^ $past(bin_in[0]))
        })
    );

    // gray_out[3] captures the previous cycle's bin_in[3].
    check_gray_bit3_encoding: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (gray_out[3] == $past(bin_in[3]))
    );

    // gray_out[2] is the previous cycle's bin_in[3] XOR bin_in[2].
    check_gray_bit2_encoding: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (gray_out[2] == ($past(bin_in[3]) ^ $past(bin_in[2])))
    );

    // gray_out[1] is the previous cycle's bin_in[2] XOR bin_in[1].
    check_gray_bit1_encoding: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (gray_out[1] == ($past(bin_in[2]) ^ $past(bin_in[1])))
    );

    // gray_out[0] is the previous cycle's bin_in[1] XOR bin_in[0].
    check_gray_bit0_encoding: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (gray_out[0] == ($past(bin_in[1]) ^ $past(bin_in[0])))
    );

endmodule