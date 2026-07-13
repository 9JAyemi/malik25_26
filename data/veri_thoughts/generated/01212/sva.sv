module dec_table_sva (
    input logic [2:0] address,
    input logic       clock,
    input logic [15:0] q
);

    // q equals 1 shifted by address into the low byte on every clock
    check_decode_shift: assert property (
        @(posedge clock) q == (16'h0001 << address)
    );

    // Upper byte of q is always zero
    check_upper_zero: assert property (
        @(posedge clock) q[15:8] == 8'h00
    );

    // Exactly one bit set in the lower byte
    check_lower_onehot: assert property (
        @(posedge clock) $onehot(q[7:0])
    );

    // Address 0 maps to 0x0001
    map_addr_000: assert property (
        @(posedge clock) (address == 3'b000) |-> (q == 16'h0001)
    );

    // Address 1 maps to 0x0002
    map_addr_001: assert property (
        @(posedge clock) (address == 3'b001) |-> (q == 16'h0002)
    );

    // Address 2 maps to 0x0004
    map_addr_010: assert property (
        @(posedge clock) (address == 3'b010) |-> (q == 16'h0004)
    );

    // Address 3 maps to 0x0008
    map_addr_011: assert property (
        @(posedge clock) (address == 3'b011) |-> (q == 16'h0008)
    );

    // Address 4 maps to 0x0010
    map_addr_100: assert property (
        @(posedge clock) (address == 3'b100) |-> (q == 16'h0010)
    );

    // Address 5 maps to 0x0020
    map_addr_101: assert property (
        @(posedge clock) (address == 3'b101) |-> (q == 16'h0020)
    );

    // Address 6 maps to 0x0040
    map_addr_110: assert property (
        @(posedge clock) (address == 3'b110) |-> (q == 16'h0040)
    );

    // Address 7 maps to 0x0080
    map_addr_111: assert property (
        @(posedge clock) (address == 3'b111) |-> (q == 16'h0080)
    );

endmodule