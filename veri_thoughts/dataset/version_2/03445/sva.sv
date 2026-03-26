module address_to_value_assertions (
    input logic [14:0] address,
    input logic        clock,
    input logic [11:0] q
);

    // q must match the previous cycle's address mapping.
    check_q_matches_previous_address: assert property (
        @(posedge clock)
        1'b1 |=> (q == (($past(address) >= 15'd4096) ? 12'b0 : $past(address[11:0])))
    );

    // Out-of-range addresses must drive q to zero on the next clock.
    check_zero_for_out_of_range_address: assert property (
        @(posedge clock)
        (address >= 15'd4096) |=> (q == 12'b0)
    );

    // In-range addresses must pass their low 12 bits to q on the next clock.
    check_passthrough_for_in_range_address: assert property (
        @(posedge clock)
        (address < 15'd4096) |=> (q == $past(address[11:0]))
    );

    // The highest in-range address must pass through unchanged.
    check_boundary_4095_passthrough: assert property (
        @(posedge clock)
        (address == 15'd4095) |=> (q == 12'hFFF)
    );

    // The first out-of-range address must map to zero.
    check_boundary_4096_zeroed: assert property (
        @(posedge clock)
        (address == 15'd4096) |=> (q == 12'b0)
    );

endmodule