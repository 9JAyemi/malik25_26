module top_module_sva (
    input  logic        clk,
    input  logic        up_down,
    input  logic        load,
    input  logic        reset,    // active-HIGH, synchronous
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic        EQ,
    input  logic        GT,
    input  logic        LT,
    // Internal top-level nets
    input  logic [3:0]  D,
    input  logic [3:0]  Q
);

    ///// Top-level D mux /////
    // D selects A when load=1 else Q.
    check_d_mux_select: assert property (
        @(posedge clk) disable iff (reset) D == (load ? A : Q)
    );

    ///// Up/down counter sequencing /////
    // On reset assertion, Q clears to 0 on next cycle.
    check_q_reset_next: assert property (
        @(posedge clk) reset |=> (Q == 4'b0000)
    );

    // With load asserted (no reset), next Q captures A.
    check_q_load_captures_a: assert property (
        @(posedge clk) disable iff (reset) load |=> (Q == $past(A))
    );

    // With up_down=1 and load=0, next Q increments by 1 (mod 16).
    check_q_increments: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down) |=> (Q == $past(Q) + 4'd1)
    );

    // With up_down=0 and load=0, next Q decrements by 1 (mod 16).
    check_q_decrements: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down) |=> (Q == $past(Q) - 4'd1)
    );

    // Increment wraps from 15 to 0.
    check_q_inc_wrap: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down && ($past(Q) == 4'hF)) |=> (Q == 4'h0)
    );

    // Decrement wraps from 0 to 15.
    check_q_dec_wrap: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down && ($past(Q) == 4'h0)) |=> (Q == 4'hF)
    );

    ///// Comparator correctness /////
    // EQ reflects (Q == B).
    check_cmp_eq: assert property (
        @(posedge clk) disable iff (reset) (EQ == (Q == B))
    );

    // GT reflects (Q > B).
    check_cmp_gt: assert property (
        @(posedge clk) disable iff (reset) (GT == (Q > B))
    );

    // LT reflects (Q < B).
    check_cmp_lt: assert property (
        @(posedge clk) disable iff (reset) (LT == (Q < B))
    );

    // Exactly one of EQ/GT/LT is HIGH.
    check_cmp_onehot: assert property (
        @(posedge clk) disable iff (reset) $onehot({EQ, GT, LT})
    );

    // After reset, comparator reflects comparison of zero vs B on next cycle.
    check_cmp_after_reset_zero: assert property (
        @(posedge clk) reset |=> (EQ == (4'd0 == B)) && (GT == 1'b0) && (LT == (4'd0 < B))
    );

endmodule