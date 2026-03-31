module binary_to_gray_sva (
    input logic [3:0] binary_in,
    input logic       clk,
    input logic [3:0] gray_out
);

    // gray_out[3] captures the previous cycle binary_in[3].
    check_gray_bit3_maps_prev_bit3: assert property (
        @(posedge clk) disable iff ($initstate)
        gray_out[3] == $past(binary_in[3])
    );

    // gray_out[2] captures the previous cycle XOR of binary_in[3] and binary_in[2].
    check_gray_bit2_maps_prev_xor: assert property (
        @(posedge clk) disable iff ($initstate)
        gray_out[2] == ($past(binary_in[3]) ^ $past(binary_in[2]))
    );

    // gray_out[1] captures the previous cycle XOR of binary_in[2] and binary_in[1].
    check_gray_bit1_maps_prev_xor: assert property (
        @(posedge clk) disable iff ($initstate)
        gray_out[1] == ($past(binary_in[2]) ^ $past(binary_in[1]))
    );

    // gray_out[0] captures the previous cycle XOR of binary_in[1] and binary_in[0].
    check_gray_bit0_maps_prev_xor: assert property (
        @(posedge clk) disable iff ($initstate)
        gray_out[0] == ($past(binary_in[1]) ^ $past(binary_in[0]))
    );

    // The full gray output matches the previous cycle binary input encoding.
    check_gray_vector_maps_prev_binary: assert property (
        @(posedge clk) disable iff ($initstate)
        gray_out == {
            $past(binary_in[3]),
            ($past(binary_in[3]) ^ $past(binary_in[2])),
            ($past(binary_in[2]) ^ $past(binary_in[1])),
            ($past(binary_in[1]) ^ $past(binary_in[0]))
        }
    );

endmodule