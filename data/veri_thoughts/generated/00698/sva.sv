module up_down_counter_sva (
    input  logic [3:0] LOAD,
    input  logic       UP_DOWN,
    input  logic       CLK,
    input  logic       RESET,
    input  logic [3:0] COUNT
);
    ///// Reset behavior /////
    // While RESET is asserted, COUNT must be 0.
    check_reset_clears_count: assert property (
        @(posedge CLK) RESET |-> (COUNT == 4'd0)
    );

    ///// Load behavior /////
    // On non-zero LOAD, COUNT is updated to LOAD on the next clock.
    check_load_updates_count: assert property (
        @(posedge CLK) disable iff (RESET)
            (LOAD != 4'd0) |=> (RESET || (COUNT == $past(LOAD)))
    );

    ///// Counting behavior /////
    // With LOAD == 0 and UP_DOWN == 1, COUNT increments by 1 on the next clock.
    check_increment_when_up: assert property (
        @(posedge CLK) disable iff (RESET)
            (LOAD == 4'd0 && (UP_DOWN == 1'b1)) |=> (RESET || (COUNT == ($past(COUNT) + 4'd1)))
    );

    // With LOAD == 0 and UP_DOWN == 0, COUNT decrements by 1 on the next clock.
    check_decrement_when_down: assert property (
        @(posedge CLK) disable iff (RESET)
            (LOAD == 4'd0 && (UP_DOWN == 1'b0)) |=> (RESET || (COUNT == ($past(COUNT) - 4'd1)))
    );

    ///// Wrap-around checks /////
    // Incrementing from 4'hF wraps to 4'h0 when LOAD == 0 and UP_DOWN == 1.
    check_wrap_on_increment: assert property (
        @(posedge CLK) disable iff (RESET)
            (LOAD == 4'd0 && (UP_DOWN == 1'b1) && ($past(COUNT) == 4'hF)) |=> (RESET || (COUNT == 4'h0))
    );

    // Decrementing from 4'h0 wraps to 4'hF when LOAD == 0 and UP_DOWN == 0.
    check_wrap_on_decrement: assert property (
        @(posedge CLK) disable iff (RESET)
            (LOAD == 4'd0 && (UP_DOWN == 1'b0) && ($past(COUNT) == 4'h0)) |=> (RESET || (COUNT == 4'hF))
    );
endmodule