module top_module_sva (
    input logic        CLK,
    input logic        LOAD,
    input logic        UP,
    input logic        DOWN,
    input logic [15:0] Y,
    input logic [3:0]  Q,
    input logic [15:0] AND_output
);

    // LOAD clears the counter on the next clock.
    check_load_clears_q: assert property (
        @(posedge CLK) LOAD |=> (Q == 4'b0000)
    );

    // With LOAD low, UP increments Q and has priority over DOWN.
    check_up_increments_q: assert property (
        @(posedge CLK) (!LOAD && UP && (Q != 4'hF)) |=> (Q == ($past(Q) + 4'h1))
    );

    // With LOAD low, UP wraps Q from 15 back to 0.
    check_up_wraps_q: assert property (
        @(posedge CLK) (!LOAD && UP && (Q == 4'hF)) |=> (Q == 4'h0)
    );

    // With LOAD and UP low, DOWN decrements Q.
    check_down_decrements_q: assert property (
        @(posedge CLK) (!LOAD && !UP && DOWN && (Q != 4'h0)) |=> (Q == ($past(Q) - 4'h1))
    );

    // With LOAD and UP low, DOWN wraps Q from 0 to 15.
    check_down_wraps_q: assert property (
        @(posedge CLK) (!LOAD && !UP && DOWN && (Q == 4'h0)) |=> (Q == 4'hF)
    );

    // With no control asserted, Q holds its value.
    check_q_holds_without_controls: assert property (
        @(posedge CLK) (!LOAD && !UP && !DOWN) |=> (Q == $past(Q))
    );

    // Y decodes Q[1:0] into a one-hot 16-bit value.
    check_decoder_matches_q: assert property (
        @(posedge CLK) Y == (16'h0001 << Q[1:0])
    );

    // AND_output is Y AND zero-extended Q.
    check_and_output_relation: assert property (
        @(posedge CLK) AND_output == (Y & {12'h000, Q})
    );

endmodule