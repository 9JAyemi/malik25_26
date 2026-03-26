module counter_sva (
    input logic       clk,
    input logic [3:0] out
);

    // Value 4 jumps to 9 on the next clock.
    check_jump_from_four_to_nine: assert property (
        @(posedge clk) (out == 4'd4) |=> (out == 4'd9)
    );

    // Value 15 wraps to 0 on the next clock.
    check_wrap_from_fifteen_to_zero: assert property (
        @(posedge clk) (out == 4'd15) |=> (out == 4'd0)
    );

    // All other values increment by one on the next clock.
    check_increment_for_normal_states: assert property (
        @(posedge clk) ((out != 4'd4) && (out != 4'd15)) |=> (out == ($past(out) + 4'd1))
    );

    // After the 4-to-9 jump, the following value is 10.
    check_continue_after_four_jump: assert property (
        @(posedge clk) (out == 4'd4) |=> ##1 (out == 4'd10)
    );

    // After the 15-to-0 wrap, the following value is 1.
    check_continue_after_fifteen_wrap: assert property (
        @(posedge clk) (out == 4'd15) |=> ##1 (out == 4'd1)
    );

endmodule