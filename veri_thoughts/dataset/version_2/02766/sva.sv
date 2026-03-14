module priority_encoder_sva (
    input logic clk,
    input logic [7:0] in,
    input logic [2:0] pos
);
    // If in[7] is 1, pos must be 7 (highest priority).
    check_priority_bit7: assert property (
        @(posedge clk) in[7] |-> (pos == 3'd7)
    );

    // If in[6] is 1 and in[7] is 0, pos must be 6.
    check_priority_bit6: assert property (
        @(posedge clk) (!in[7] && in[6]) |-> (pos == 3'd6)
    );

    // If in[5] is 1 and in[7:6] are 0, pos must be 5.
    check_priority_bit5: assert property (
        @(posedge clk) ((in[7:6] == 2'b00) && in[5]) |-> (pos == 3'd5)
    );

    // If in[4] is 1 and in[7:5] are 0, pos must be 4.
    check_priority_bit4: assert property (
        @(posedge clk) ((in[7:5] == 3'b000) && in[4]) |-> (pos == 3'd4)
    );

    // If in[3] is 1 and in[7:4] are 0, pos must be 3.
    check_priority_bit3: assert property (
        @(posedge clk) ((in[7:4] == 4'b0000) && in[3]) |-> (pos == 3'd3)
    );

    // If in[2] is 1 and in[7:3] are 0, pos must be 2.
    check_priority_bit2: assert property (
        @(posedge clk) ((in[7:3] == 5'b00000) && in[2]) |-> (pos == 3'd2)
    );

    // If in[1] is 1 and in[7:2] are 0, pos must be 1.
    check_priority_bit1: assert property (
        @(posedge clk) ((in[7:2] == 6'b000000) && in[1]) |-> (pos == 3'd1)
    );

    // If only in[0] is 1 (no higher bits), pos must be 0.
    check_priority_bit0: assert property (
        @(posedge clk) ((in[7:1] == 7'b0000000) && in[0]) |-> (pos == 3'd0)
    );

    // If all inputs are 0, pos must be 0.
    check_zero_input: assert property (
        @(posedge clk) (in == 8'b0000_0000) |-> (pos == 3'd0)
    );

    // If pos is 7, then in[7] must be 1.
    check_inverse_pos7_requires_in7: assert property (
        @(posedge clk) (pos == 3'd7) |-> in[7]
    );

    // If pos is 6, then in[7] must be 0 and in[6] must be 1.
    check_inverse_pos6_requires_in6_and_no7: assert property (
        @(posedge clk) (pos == 3'd6) |-> (!in[7] && in[6])
    );

    // If pos is 0, no higher bits [7:1] may be set.
    check_inverse_pos0_blocks_higher: assert property (
        @(posedge clk) (pos == 3'd0) |-> (in[7:1] == 7'b0000000)
    );
endmodule