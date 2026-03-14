module sum_first_last_16_bits_sva (
    input logic [31:0] in_signal,
    input logic [15:0] out_signal
);
    // Output equals sum of upper and lower 16 bits (mod 2^16).
    check_sum_definition: assert property (
        @(posedge in_signal[0]) out_signal == (in_signal[31:16] + in_signal[15:0])
    );

    // If upper 16 bits are zero, output equals lower 16 bits.
    check_zero_upper_passthrough: assert property (
        @(posedge in_signal[0]) (in_signal[31:16] == 16'h0000) |=> (out_signal == in_signal[15:0])
    );

    // If lower 16 bits are zero, output equals upper 16 bits.
    check_zero_lower_passthrough: assert property (
        @(posedge in_signal[0]) (in_signal[15:0] == 16'h0000) |=> (out_signal == in_signal[31:16])
    );

    // If upper half is all ones, output equals lower minus one (mod 2^16).
    check_all_ones_upper_minus_one: assert property (
        @(posedge in_signal[0]) (in_signal[31:16] == 16'hFFFF) |=> (out_signal == (in_signal[15:0] - 16'd1))
    );

    // If lower half is all ones, output equals upper minus one (mod 2^16).
    check_all_ones_lower_minus_one: assert property (
        @(posedge in_signal[0]) (in_signal[15:0] == 16'hFFFF) |=> (out_signal == (in_signal[31:16] - 16'd1))
    );

    // If both halves are all ones, output equals 16'hFFFE.
    check_all_ones_both_fffe: assert property (
        @(posedge in_signal[0]) (in_signal == 32'hFFFF_FFFF) |=> (out_signal == 16'hFFFE)
    );

    // Output LSB equals XOR of LSBs of the two halves.
    check_lsb_xor_of_halves: assert property (
        @(posedge in_signal[0]) out_signal[0] == (in_signal[16] ^ in_signal[0])
    );

    // If halves are equal, output equals value left-shifted by 1 (mod 2^16).
    check_equal_halves_left_shift: assert property (
        @(posedge in_signal[0]) (in_signal[31:16] == in_signal[15:0]) |=> (out_signal == (in_signal[15:0] << 1))
    );
endmodule