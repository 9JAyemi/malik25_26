module binary_to_gray_sva (
    input logic        clk,
    input logic        rst,
    input logic [31:0] data_in,
    input logic [7:0]  data_out
);

    // After a reset cycle, the output is zero.
    check_reset_clears_output: assert property (
        @(posedge clk) disable iff (rst)
        $past(rst) |-> (data_out == 8'h00)
    );

    // The output matches the previous cycle's Gray-coded low 8 input bits.
    check_gray_full_mapping: assert property (
        @(posedge clk) disable iff (rst)
        $past(!rst) |-> (data_out == {
            $past(data_in[7]),
            ($past(data_in[7]) ^ $past(data_in[6])),
            ($past(data_in[6]) ^ $past(data_in[5])),
            ($past(data_in[5]) ^ $past(data_in[4])),
            ($past(data_in[4]) ^ $past(data_in[3])),
            ($past(data_in[3]) ^ $past(data_in[2])),
            ($past(data_in[2]) ^ $past(data_in[1])),
            ($past(data_in[1]) ^ $past(data_in[0]))
        })
    );

    // Output bit 7 passes through previous input bit 7.
    check_gray_bit7: assert property (
        @(posedge clk) disable iff (rst)
        $past(!rst) |-> (data_out[7] == $past(data_in[7]))
    );

    // Output bit 6 is previous input bits 7 and 6 XORed.
    check_gray_bit6: assert property (
        @(posedge clk) disable iff (rst)
        $past(!rst) |-> (data_out[6] == ($past(data_in[7]) ^ $past(data_in[6])))
    );

    // Output bit 5 is previous input bits 6 and 5 XORed.
    check_gray_bit5: assert property (
        @(posedge clk) disable iff (rst)
        $past(!rst) |-> (data_out[5] == ($past(data_in[6]) ^ $past(data_in[5])))
    );

    // Output bit 4 is previous input bits 5 and 4 XORed.
    check_gray_bit4: assert property (
        @(posedge clk) disable iff (rst)
        $past(!rst) |-> (data_out[4] == ($past(data_in[5]) ^ $past(data_in[4])))
    );

    // Output bit 3 is previous input bits 4 and 3 XORed.
    check_gray_bit3: assert property (
        @(posedge clk) disable iff (rst)
        $past(!rst) |-> (data_out[3] == ($past(data_in[4]) ^ $past(data_in[3])))
    );

    // Output bit 2 is previous input bits 3 and 2 XORed.
    check_gray_bit2: assert property (
        @(posedge clk) disable iff (rst)
        $past(!rst) |-> (data_out[2] == ($past(data_in[3]) ^ $past(data_in[2])))
    );

    // Output bit 1 is previous input bits 2 and 1 XORed.
    check_gray_bit1: assert property (
        @(posedge clk) disable iff (rst)
        $past(!rst) |-> (data_out[1] == ($past(data_in[2]) ^ $past(data_in[1])))
    );

    // Output bit 0 is previous input bits 1 and 0 XORed.
    check_gray_bit0: assert property (
        @(posedge clk) disable iff (rst)
        $past(!rst) |-> (data_out[0] == ($past(data_in[1]) ^ $past(data_in[0])))
    );

    // Repeated low 8 input bits produce a repeated output value.
    check_same_input_same_output: assert property (
        @(posedge clk) disable iff (rst)
        $past(!rst) && $past(!rst, 2) &&
        ($past(data_in[7:0]) == $past(data_in[7:0], 2))
        |-> (data_out == $past(data_out))
    );

endmodule