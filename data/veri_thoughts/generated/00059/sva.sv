module binary_to_gray_assertions(
    input logic [3:0] binary,
    input logic       clk,
    input logic [3:0] gray
);

    // Gray output is the registered binary-to-Gray conversion from the prior clock.
    check_gray_conversion: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> gray == ($past(binary) ^ ($past(binary) >> 1))
    );

    // Gray[3] matches the prior binary MSB.
    check_gray_bit3: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> gray[3] == $past(binary[3])
    );

    // Gray[2] is the XOR of the prior binary[3] and binary[2].
    check_gray_bit2: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> gray[2] == ($past(binary[3]) ^ $past(binary[2]))
    );

    // Gray[1] is the XOR of the prior binary[2] and binary[1].
    check_gray_bit1: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> gray[1] == ($past(binary[2]) ^ $past(binary[1]))
    );

    // Gray[0] is the XOR of the prior binary[1] and binary[0].
    check_gray_bit0: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> gray[0] == ($past(binary[1]) ^ $past(binary[0]))
    );

endmodule