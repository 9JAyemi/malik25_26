module address_to_signal_sva (
    input logic [9:0]  address,
    input logic        clock,
    input logic [11:0] q
);
    // When clock is HIGH, q equals bitwise NOT of {address,2'b00}.
    check_q_full_posedge_map: assert property (
        @(posedge clock) q == ~{address, 2'b00}
    );

    // When clock is LOW, q equals {address,2'b00}.
    check_q_full_negedge_map: assert property (
        @(negedge clock) q == {address, 2'b00}
    );

    // When clock is HIGH, the low 2 bits of q are 2'b11 (invert of 2'b00).
    check_lowbits_posedge_ones: assert property (
        @(posedge clock) q[1:0] == 2'b11
    );

    // When clock is LOW, the low 2 bits of q are 2'b00.
    check_lowbits_negedge_zeros: assert property (
        @(negedge clock) q[1:0] == 2'b00
    );

    // When clock is HIGH, upper 10 bits of q are bitwise NOT of address.
    check_upper_posedge_inv_address: assert property (
        @(posedge clock) q[11:2] == ~address
    );

    // When clock is LOW, upper 10 bits of q equal address.
    check_upper_negedge_address: assert property (
        @(negedge clock) q[11:2] == address
    );

    // When clock is HIGH, XOR of q[11:2] and address is all ones.
    check_upper_xor_posedge_allones: assert property (
        @(posedge clock) (q[11:2] ^ address) == 10'h3FF
    );

    // When clock is LOW, XOR of q[11:2] and address is all zeros.
    check_upper_xor_negedge_allzeros: assert property (
        @(negedge clock) (q[11:2] ^ address) == 10'h000
    );
endmodule