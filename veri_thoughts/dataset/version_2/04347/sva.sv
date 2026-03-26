module bin_to_gray_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] bin,
    input logic [3:0] gray
);

    // Reset drives gray to zero on the following clock.
    check_reset_clears_gray: assert property (
        @(posedge clk) rst |=> (gray == 4'b0000)
    );

    // Gray matches the registered binary-to-Gray conversion.
    check_gray_matches_registered_conversion: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (gray == ($past(bin) ^ ($past(bin) >> 1)))
    );

    // Gray[3] equals the previous binary MSB.
    check_gray_bit3: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (gray[3] == $past(bin[3]))
    );

    // Gray[2] equals the previous bin[3] xor bin[2].
    check_gray_bit2: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (gray[2] == ($past(bin[3]) ^ $past(bin[2])))
    );

    // Gray[1] equals the previous bin[2] xor bin[1].
    check_gray_bit1: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (gray[1] == ($past(bin[2]) ^ $past(bin[1])))
    );

    // Gray[0] equals the previous bin[1] xor bin[0].
    check_gray_bit0: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (gray[0] == ($past(bin[1]) ^ $past(bin[0])))
    );

endmodule