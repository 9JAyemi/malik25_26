module priority_encoder_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] in,
    input logic [3:0] valid,
    input logic [1:0] pos
);

    // pos must be zero while reset is asserted low.
    check_reset_clears_pos: assert property (
        @(posedge clk) !reset |-> (pos == 2'b00)
    );

    // valid[3] has highest priority and selects position 3.
    check_valid3_priority: assert property (
        @(posedge clk) disable iff (!reset)
        valid[3] |=> (pos == 2'b11)
    );

    // valid[2] selects position 2 when valid[3] is not set.
    check_valid2_priority: assert property (
        @(posedge clk) disable iff (!reset)
        (!valid[3] && valid[2]) |=> (pos == 2'b10)
    );

    // valid[1] selects position 1 when higher priority valids are not set.
    check_valid1_priority: assert property (
        @(posedge clk) disable iff (!reset)
        (!valid[3] && !valid[2] && valid[1]) |=> (pos == 2'b01)
    );

    // valid[0] selects position 0 when it is the highest valid bit.
    check_valid0_priority: assert property (
        @(posedge clk) disable iff (!reset)
        (!valid[3] && !valid[2] && !valid[1] && valid[0]) |=> (pos == 2'b00)
    );

    // No valid bits set drives the encoded position to zero.
    check_no_valid_defaults_zero: assert property (
        @(posedge clk) disable iff (!reset)
        (!valid[3] && !valid[2] && !valid[1] && !valid[0]) |=> (pos == 2'b00)
    );

endmodule