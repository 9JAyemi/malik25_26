module binary_to_gray_sva (
    input logic [3:0] binary_in,
    input logic       clk,
    input logic [3:0] gray_out
);

    // gray_out must equal the prior cycle's binary input converted to Gray code.
    check_gray_vector: assert property (
        @(posedge clk)
        1'b1 |=> gray_out == {
            $past(binary_in[3]),
            ($past(binary_in[3]) ^ $past(binary_in[2])),
            ($past(binary_in[2]) ^ $past(binary_in[1])),
            ($past(binary_in[1]) ^ $past(binary_in[0]))
        }
    );

    // gray_out[3] must copy the prior cycle's binary_in[3].
    check_gray_msb: assert property (
        @(posedge clk)
        1'b1 |=> gray_out[3] == $past(binary_in[3])
    );

    // gray_out[2] must be the prior cycle XOR of binary_in[3] and binary_in[2].
    check_gray_bit2: assert property (
        @(posedge clk)
        1'b1 |=> gray_out[2] == ($past(binary_in[3]) ^ $past(binary_in[2]))
    );

    // gray_out[1] must be the prior cycle XOR of binary_in[2] and binary_in[1].
    check_gray_bit1: assert property (
        @(posedge clk)
        1'b1 |=> gray_out[1] == ($past(binary_in[2]) ^ $past(binary_in[1]))
    );

    // gray_out[0] must be the prior cycle XOR of binary_in[1] and binary_in[0].
    check_gray_lsb: assert property (
        @(posedge clk)
        1'b1 |=> gray_out[0] == ($past(binary_in[1]) ^ $past(binary_in[0]))
    );

endmodule