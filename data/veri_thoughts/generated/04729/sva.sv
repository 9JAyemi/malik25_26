module binary_to_gray_assertions (
    input logic [3:0] binary_in,
    input logic       clk,
    input logic [3:0] gray_out
);

    // gray_out[3] matches the previous cycle binary_in[3].
    check_gray_msb: assert property (
        @(posedge clk) 1'b1 |=> gray_out[3] == $past(binary_in[3])
    );

    // gray_out[2] matches the previous cycle binary_in[3] ^ binary_in[2].
    check_gray_bit2: assert property (
        @(posedge clk) 1'b1 |=> gray_out[2] == ($past(binary_in[3]) ^ $past(binary_in[2]))
    );

    // gray_out[1] matches the previous cycle binary_in[2] ^ binary_in[1].
    check_gray_bit1: assert property (
        @(posedge clk) 1'b1 |=> gray_out[1] == ($past(binary_in[2]) ^ $past(binary_in[1]))
    );

    // gray_out[0] matches the previous cycle binary_in[1] ^ binary_in[0].
    check_gray_lsb: assert property (
        @(posedge clk) 1'b1 |=> gray_out[0] == ($past(binary_in[1]) ^ $past(binary_in[0]))
    );

    // gray_out matches the previous cycle Gray-code conversion of binary_in.
    check_gray_bus: assert property (
        @(posedge clk) 1'b1 |=> gray_out == {
            $past(binary_in[3]),
            ($past(binary_in[3]) ^ $past(binary_in[2])),
            ($past(binary_in[2]) ^ $past(binary_in[1])),
            ($past(binary_in[1]) ^ $past(binary_in[0]))
        }
    );

endmodule