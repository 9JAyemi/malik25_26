module bin_to_gray_converter_sva (
    input logic       clk,
    input logic [3:0] bin,
    input logic [3:0] gray
);

    // Gray matches the prior cycle binary-to-Gray conversion.
    check_gray_registered_mapping: assert property (
        @(posedge clk) 1'b1 |=> (gray === ({1'b0, $past(bin[3:1])} ^ $past(bin)))
    );

    // Gray[3] is the registered MSB of bin.
    check_gray_bit3_mapping: assert property (
        @(posedge clk) 1'b1 |=> (gray[3] === $past(bin[3]))
    );

    // Gray[2] is the registered XOR of bin[3] and bin[2].
    check_gray_bit2_mapping: assert property (
        @(posedge clk) 1'b1 |=> (gray[2] === ($past(bin[3]) ^ $past(bin[2])))
    );

    // Gray[1] is the registered XOR of bin[2] and bin[1].
    check_gray_bit1_mapping: assert property (
        @(posedge clk) 1'b1 |=> (gray[1] === ($past(bin[2]) ^ $past(bin[1])))
    );

    // Gray[0] is the registered XOR of bin[1] and bin[0].
    check_gray_bit0_mapping: assert property (
        @(posedge clk) 1'b1 |=> (gray[0] === ($past(bin[1]) ^ $past(bin[0])))
    );

endmodule