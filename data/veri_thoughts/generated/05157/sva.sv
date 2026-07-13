module RegisterAdd_3_sva (
    input logic clk,
    input logic rst,
    input logic load,
    input logic [0:0] D,
    input logic [0:0] Q
);

    // A sampled active reset must correspond to a low Q.
    check_reset_clears_q: assert property (
        @(posedge clk) disable iff ($initstate)
        rst |-> (Q == 1'b0)
    );

    // A reset cycle leaves Q low at the next clock sample.
    check_reset_keeps_q_low_next_cycle: assert property (
        @(posedge clk) disable iff ($initstate)
        rst |=> (Q == 1'b0)
    );

    // Loading a zero writes zero into Q.
    check_load_zero_captures_zero: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (load && (D == 1'b0)) |=> (Q == 1'b0)
    );

    // With load low, a zero in Q stays zero.
    check_zero_holds_when_not_loading: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!load && (Q == 1'b0)) |=> (Q == 1'b0)
    );

    // A high Q must come from loading a one or holding a previous one.
    check_q_high_has_valid_source: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (Q == 1'b1) |-> (
            !$past(rst) &&
            (($past(load) && ($past(D) == 1'b1)) ||
             (!$past(load) && ($past(Q) == 1'b1)))
        )
    );

    // A rise on Q can only be caused by loading a one on the prior cycle.
    check_q_rise_requires_load_one: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (($past(Q) == 1'b0) && (Q == 1'b1)) |-> (
            !$past(rst) && $past(load) && ($past(D) == 1'b1)
        )
    );

endmodule