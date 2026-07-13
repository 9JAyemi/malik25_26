module niosII_system_nios2_0_nios2_oci_td_mode_sva (
    input logic [8:0] ctrl,
    input logic [3:0] td_mode
);
    // Analysis: no clock/reset in RTL; pure combinational decode of ctrl[7:5] to td_mode.
    // Note: Assertions are sampled on posedge of ctrl[0] as a proxy clock.

    ///// Decode mapping /////
    // ctrl[7:5]==000 -> td_mode=0000
    decode_000: assert property (
        @(posedge ctrl[0]) (ctrl[7:5] == 3'b000) |-> (td_mode == 4'b0000)
    );
    // ctrl[7:5]==001 -> td_mode=1000
    decode_001: assert property (
        @(posedge ctrl[0]) (ctrl[7:5] == 3'b001) |-> (td_mode == 4'b1000)
    );
    // ctrl[7:5]==010 -> td_mode=0100
    decode_010: assert property (
        @(posedge ctrl[0]) (ctrl[7:5] == 3'b010) |-> (td_mode == 4'b0100)
    );
    // ctrl[7:5]==011 -> td_mode=1100
    decode_011: assert property (
        @(posedge ctrl[0]) (ctrl[7:5] == 3'b011) |-> (td_mode == 4'b1100)
    );
    // ctrl[7:5]==100 -> td_mode=0010
    decode_100: assert property (
        @(posedge ctrl[0]) (ctrl[7:5] == 3'b100) |-> (td_mode == 4'b0010)
    );
    // ctrl[7:5]==101 -> td_mode=1010
    decode_101: assert property (
        @(posedge ctrl[0]) (ctrl[7:5] == 3'b101) |-> (td_mode == 4'b1010)
    );
    // ctrl[7:5]==110 -> td_mode=0101
    decode_110: assert property (
        @(posedge ctrl[0]) (ctrl[7:5] == 3'b110) |-> (td_mode == 4'b0101)
    );
    // ctrl[7:5]==111 -> td_mode=1111
    decode_111: assert property (
        @(posedge ctrl[0]) (ctrl[7:5] == 3'b111) |-> (td_mode == 4'b1111)
    );

    ///// Bit-level relationships implied by the case /////
    // td_mode[3] mirrors ctrl[5]
    bit_map_msb: assert property (
        @(posedge ctrl[0]) td_mode[3] == ctrl[5]
    );
    // td_mode[2] mirrors ctrl[6]
    bit_map_b2: assert property (
        @(posedge ctrl[0]) td_mode[2] == ctrl[6]
    );
    // td_mode[0] equals ctrl[7] & ctrl[6]
    bit_map_b0: assert property (
        @(posedge ctrl[0]) td_mode[0] == (ctrl[7] & ctrl[6])
    );
    // td_mode[1] equals ctrl[7] & (~ctrl[6] | ctrl[5])
    bit_map_b1: assert property (
        @(posedge ctrl[0]) td_mode[1] == (ctrl[7] & (~ctrl[6] | ctrl[5]))
    );

    ///// Consistency checks derived from mapping /////
    // If td_mode[0] is 1 then td_mode[2] must be 1
    consistency_b0_implies_b2: assert property (
        @(posedge ctrl[0]) td_mode[0] |-> td_mode[2]
    );
    // When td_mode is 0000, ctrl[7:5] must be 000
    inverse_000: assert property (
        @(posedge ctrl[0]) (td_mode == 4'b0000) |-> (ctrl[7:5] == 3'b000)
    );
    // When td_mode is 1000, ctrl[7:5] must be 001
    inverse_1000: assert property (
        @(posedge ctrl[0]) (td_mode == 4'b1000) |-> (ctrl[7:5] == 3'b001)
    );
    // When td_mode is 1111, ctrl[7:5] must be 111
    inverse_1111: assert property (
        @(posedge ctrl[0]) (td_mode == 4'b1111) |-> (ctrl[7:5] == 3'b111)
    );
endmodule