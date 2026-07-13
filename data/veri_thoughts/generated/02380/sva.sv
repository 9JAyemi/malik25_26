module priority_encoder_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] in,
    input logic [1:0] pos
);

    ///// Functional mapping /////
    // If bit 3 is set, pos must be 2'b11.
    map_bit3_priority: assert property (
        @(posedge CLK) disable iff (!RESETn) in[3] |-> (pos == 2'b11)
    );

    // If bit 2 is set and bit 3 is clear, pos must be 2'b10.
    map_bit2_priority: assert property (
        @(posedge CLK) disable iff (!RESETn) (!in[3] && in[2]) |-> (pos == 2'b10)
    );

    // If bit 1 is set and bits 3:2 are clear, pos must be 2'b01.
    map_bit1_priority: assert property (
        @(posedge CLK) disable iff (!RESETn) (!in[3] && !in[2] && in[1]) |-> (pos == 2'b01)
    );

    // If only bit 0 is the highest set (bits 3:1 clear and bit 0 set), pos must be 2'b00.
    map_bit0_priority: assert property (
        @(posedge CLK) disable iff (!RESETn) (!in[3] && !in[2] && !in[1] && in[0]) |-> (pos == 2'b00)
    );

    // If input is zero, pos must be 2'b00.
    map_zero_input: assert property (
        @(posedge CLK) disable iff (!RESETn) (in == 4'b0000) |-> (pos == 2'b00)
    );

    ///// Inverse mapping /////
    // If pos is 2'b11, bit 3 must be set.
    inv_pos_11_implies_bit3: assert property (
        @(posedge CLK) disable iff (!RESETn) (pos == 2'b11) |-> (in[3] == 1'b1)
    );

    // If pos is 2'b10, bit 2 must be set and bit 3 must be clear.
    inv_pos_10_implies_bit2_only_higher_clear: assert property (
        @(posedge CLK) disable iff (!RESETn) (pos == 2'b10) |-> (!in[3] && in[2])
    );

    // If pos is 2'b01, bit 1 must be set and bits 3:2 must be clear.
    inv_pos_01_implies_bit1_only_higher_clear: assert property (
        @(posedge CLK) disable iff (!RESETn) (pos == 2'b01) |-> (!in[3] && !in[2] && in[1])
    );

    // If pos is 2'b00, input must be zero or bit 0 is highest set (bits 3:1 clear).
    inv_pos_00_implies_zero_or_bit0_only: assert property (
        @(posedge CLK) disable iff (!RESETn) (pos == 2'b00) |-> ((in == 4'b0000) || (!in[3] && !in[2] && !in[1] && in[0]))
    );

    ///// Full spec equivalence /////
    // pos equals the specified priority-encoder function of in.
    pos_matches_function: assert property (
        @(posedge CLK) disable iff (!RESETn)
            pos == ((in == 4'b0000) ? 2'b00 :
                    (in[3] ? 2'b11 :
                     (in[2] ? 2'b10 :
                      (in[1] ? 2'b01 :
                               2'b00))))
    );

endmodule