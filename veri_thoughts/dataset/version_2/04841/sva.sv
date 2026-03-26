module address_decoder_assertions(
    input logic [14:0] address,
    input logic        clock,
    input logic [11:0] q
);

    // Addresses below 0x0800 decode to zero on the next clock.
    check_low_range_zero: assert property (
        @(posedge clock)
        (address < 15'h0800) |=> (q == 12'h000)
    );

    // Addresses 0x0800 through 0x0FFF pass through the low 12 bits on the next clock.
    check_mid_range_passthrough: assert property (
        @(posedge clock)
        (address >= 15'h0800 && address < 15'h1000) |=> (q == $past(address[11:0]))
    );

    // Addresses 0x1000 and above decode to address[14:3] on the next clock.
    check_high_range_slice: assert property (
        @(posedge clock)
        (address >= 15'h1000) |=> (q == $past(address[14:3]))
    );

    // 0x07FF is still in the zero-decoded range.
    check_boundary_07ff: assert property (
        @(posedge clock)
        (address == 15'h07FF) |=> (q == 12'h000)
    );

    // 0x0800 is the first address that passes through its low 12 bits.
    check_boundary_0800: assert property (
        @(posedge clock)
        (address == 15'h0800) |=> (q == 12'h800)
    );

    // 0x0FFF is the last address in the pass-through range.
    check_boundary_0fff: assert property (
        @(posedge clock)
        (address == 15'h0FFF) |=> (q == 12'hFFF)
    );

    // 0x1000 is the first address that uses address[14:3].
    check_boundary_1000: assert property (
        @(posedge clock)
        (address == 15'h1000) |=> (q == 12'h200)
    );

    // 0x7FFF maps to the maximum sliced output value.
    check_boundary_7fff: assert property (
        @(posedge clock)
        (address == 15'h7FFF) |=> (q == 12'hFFF)
    );

endmodule