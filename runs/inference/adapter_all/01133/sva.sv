module address_to_signal_sva (
    input logic [9:0]  address,
    input logic        clock,
    input logic [11:0] q
);

    // q must match the RTL's address shift and optional inversion.
    check_q_matches_rtl_function: assert property (
        @(posedge clock) q == ((address << 2) ^ (clock ? 12'h000 : 12'h3FF))
    );

    // With clock low, q is the shifted address with zeros in bits [1:0].
    check_q_when_clock_low: assert property (
        @(posedge clock) !clock |-> (q == (address << 2))
    );

    // With clock high, q is the inverted shifted address with ones in bits [1:0].
    check_q_when_clock_high: assert property (
        @(posedge clock) clock |-> (q == ~(address << 2))
    );

    // The low two bits of q are always zero.
    check_q_low_bits_zero: assert property (
        @(posedge clock) q[1:0] == 2'b00
    );

    // The upper eight bits of q are either the address or its inverse.
    check_q_upper_byte_matches_address: assert property (
        @(posedge clock) q[11:2] == (clock ? ~address : address)
    );

    // The upper eight bits of q are always within the valid address range.
    check_q_upper_byte_in_valid_range: assert property (
        @(posedge clock) q[11:2] <= 8'hFF
    );

endmodule