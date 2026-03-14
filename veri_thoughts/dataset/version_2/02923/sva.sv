module decoder_3_to_8_sva (
    input logic [2:0] ABC,
    input logic [7:0] Y
);
    // ABC==000 maps to Y bit0 set.
    decode_map_000: assert property (
        @(posedge $global_clock) (ABC == 3'b000) |-> (Y == 8'b00000001)
    );

    // ABC==001 maps to Y bit1 set.
    decode_map_001: assert property (
        @(posedge $global_clock) (ABC == 3'b001) |-> (Y == 8'b00000010)
    );

    // ABC==010 maps to Y bit2 set.
    decode_map_010: assert property (
        @(posedge $global_clock) (ABC == 3'b010) |-> (Y == 8'b00000100)
    );

    // ABC==011 maps to Y bit3 set.
    decode_map_011: assert property (
        @(posedge $global_clock) (ABC == 3'b011) |-> (Y == 8'b00001000)
    );

    // ABC==100 maps to Y bit4 set.
    decode_map_100: assert property (
        @(posedge $global_clock) (ABC == 3'b100) |-> (Y == 8'b00010000)
    );

    // ABC==101 maps to Y bit5 set.
    decode_map_101: assert property (
        @(posedge $global_clock) (ABC == 3'b101) |-> (Y == 8'b00100000)
    );

    // ABC==110 maps to Y bit6 set.
    decode_map_110: assert property (
        @(posedge $global_clock) (ABC == 3'b110) |-> (Y == 8'b01000000)
    );

    // ABC==111 maps to Y bit7 set.
    decode_map_111: assert property (
        @(posedge $global_clock) (ABC == 3'b111) |-> (Y == 8'b10000000)
    );

    // Unknown ABC drives Y to zero via default case.
    unknown_input_zero_output: assert property (
        @(posedge $global_clock) $isunknown(ABC) |-> (Y == 8'b00000000)
    );

    // If ABC is fully known, Y is exactly one-hot.
    known_input_onehot_output: assert property (
        @(posedge $global_clock) !$isunknown(ABC) |-> $onehot(Y)
    );

    // Y is at most one-hot (allows zero when ABC has X/Z).
    output_at_most_onehot: assert property (
        @(posedge $global_clock) $onehot0(Y)
    );

    // Y is never X/Z because all assignments are constant literals.
    output_never_unknown: assert property (
        @(posedge $global_clock) !$isunknown(Y)
    );

    // Y==0 only occurs when ABC contains X/Z.
    zero_output_implies_unknown_input: assert property (
        @(posedge $global_clock) (Y == 8'b00000000) |-> $isunknown(ABC)
    );
endmodule