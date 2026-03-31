module signal_processor_sva (
    input logic [3:0] in,
    input logic [3:0] out
);
    // Combinational DUT with no clock/reset; sample on any input edge.

    // For in < 4, out equals in * 2 (4-bit wrap).
    check_map_lt4: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in < 4) |-> (out == (in << 1))
    );

    // For 4 <= in <= 7, out equals in * in (4-bit wrap).
    check_map_4to7: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in >= 4 && in <= 7) |-> (out == (in * in))
    );

    // For in > 7, out equals in / 2 (integer division, 4-bit wrap).
    check_map_gt7: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in > 7) |-> (out == (in >> 1))
    );

    // For in == 0, out == 0.
    check_map_in0: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in == 4'd0) |-> (out == 4'd0)
    );

    // For in == 1, out == 2.
    check_map_in1: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in == 4'd1) |-> (out == 4'd2)
    );

    // For in == 2, out == 4.
    check_map_in2: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in == 4'd2) |-> (out == 4'd4)
    );

    // For in == 3, out == 6.
    check_map_in3: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in == 4'd3) |-> (out == 4'd6)
    );

    // For in == 4, out == 16 (4-bit wrap to 0).
    check_map_in4: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in == 4'd4) |-> (out == 4'd0)
    );

    // For in == 5, out == 25 (4-bit wrap to 1).
    check_map_in5: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in == 4'd5) |-> (out == 4'd1)
    );

    // For in == 6, out == 36 (4-bit wrap to 4).
    check_map_in6: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in == 4'd6) |-> (out == 4'd4)
    );

    // For in == 7, out == 49 (4-bit wrap to 1).
    check_map_in7: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in == 4'd7) |-> (out == 4'd1)
    );

    // For in == 8, out == 4 (8 / 2).
    check_map_in8: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in == 4'd8) |-> (out == 4'd4)
    );

    // For in == 9, out == 2 (9 / 2).
    check_map_in9: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in == 4'd9) |-> (out == 4'd2)
    );

    // For in == 10, out == 0 (10 / 2).
    check_map_in10: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in == 4'd10) |-> (out == 4'd0)
    );

    // For in == 11, out == 1 (11 / 2).
    check_map_in11: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in == 4'd11) |-> (out == 4'd1)
    );

    // For in == 12, out == 4 (12 / 2).
    check_map_in12: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in == 4'd12) |-> (out == 4'd4)
    );

    // For in == 13, out == 2 (13 / 2).
    check_map_in13: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in == 4'd13) |-> (out == 4'd2)
    );

    // For in == 14, out == 0 (14 / 2).
    check_map_in14: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (in == 4'd14) |-> (out == 4'd0)
    );

    // For in == 15, out == 1 (15 / 2).
    check_map_in15: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (