module decoder_3to8_sva (
    input logic clk,
    input logic [2:0] abc,
    input logic [7:0] y
);
    // y equals the one-hot decode of abc from the previous cycle.
    check_decode_matches_prev_abc: assert property (
        @(posedge clk) $past(1'b1) |-> (y == (8'b00000001 << $past(abc)))
    );

    // y is non-zero and one-hot each cycle (after the first).
    check_y_onehot: assert property (
        @(posedge clk) $past(1'b1) |-> (y != 8'b00000000) && ((y & (y - 8'b00000001)) == 8'b00000000)
    );

    // If abc is unchanged across a cycle, y remains unchanged in the next cycle.
    check_stability_when_abc_stable: assert property (
        @(posedge clk) ($past(1'b1) && (abc == $past(abc))) |-> ##1 (y == $past(y))
    );

    // If abc changes across a cycle, y changes in the next cycle.
    check_change_propagation: assert property (
        @(posedge clk) ($past(1'b1) && (abc != $past(abc))) |-> ##1 (y != $past(y))
    );

    // When previous abc was 0, y is 00000001.
    check_low_boundary_decode: assert property (
        @(posedge clk) ($past(1'b1) && ($past(abc) == 3'd0)) |-> (y == 8'b00000001)
    );

    // When previous abc was 7, y is 10000000.
    check_high_boundary_decode: assert property (
        @(posedge clk) ($past(1'b1) && ($past(abc) == 3'd7)) |-> (y == 8'b10000000)
    );
endmodule