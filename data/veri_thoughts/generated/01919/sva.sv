module register_sva (
    input logic d,
    input logic clk,
    input logic ena,
    input logic clr,
    input logic pr,
    input logic q
);

    // clr high forces q to 0 on the next cycle.
    check_clr_forces_zero: assert property (
        @(posedge clk) disable iff (1'b0) clr |=> (q == 1'b0)
    );

    // When clr and pr are both high, clear wins and q goes to 0 next cycle.
    check_priority_clr_over_pr: assert property (
        @(posedge clk) disable iff (1'b0) (clr && pr) |=> (q == 1'b0)
    );

    // pr high (with clr low) forces q to 1 on the next cycle.
    check_pr_sets_one_when_no_clr: assert property (
        @(posedge clk) disable iff (1'b0) (!clr && pr) |=> (q == 1'b1)
    );

    // With ena and no clr/pr, q loads d on the next cycle.
    check_ena_loads_d_when_no_clr_pr: assert property (
        @(posedge clk) disable iff (1'b0) (!clr && !pr && ena) |=> (q == $past(d))
    );

    // With no clr/pr/ena, q holds its previous value.
    check_hold_when_no_ctrl: assert property (
        @(posedge clk) disable iff (1'b0) (!clr && !pr && !ena) |=> (q == $past(q))
    );

    // With pr and ena asserted (and clr low), pr has priority and q goes to 1.
    check_priority_pr_over_ena: assert property (
        @(posedge clk) disable iff (1'b0) (!clr && pr && ena) |=> (q == 1'b1)
    );

    // A rising edge on q must be caused by prior pr or a load of 1.
    check_rise_q_caused_by_pr_or_load1: assert property (
        @(posedge clk) disable iff (1'b0)
            $rose(q) |-> (($past(pr) && !$past(clr)) ||
                          (!$past(clr) && !$past(pr) && $past(ena) && ($past(d) == 1'b1)))
    );

    // A falling edge on q must be caused by prior clr or a load of 0.
    check_fall_q_caused_by_clr_or_load0: assert property (
        @(posedge clk) disable iff (1'b0)
            $fell(q) |-> ($past(clr) ||
                          (!$past(clr) && !$past(pr) && $past(ena) && ($past(d) == 1'b0)))
    );

    // When loading a 1 (ena=1, no clr/pr, d=1), q becomes 1 next cycle.
    check_load_one: assert property (
        @(posedge clk) disable iff (1'b0) (!clr && !pr && ena && d) |=> (q == 1'b1)
    );

    // When loading a 0 (ena=1, no clr/pr, d=0), q becomes 0 next cycle.
    check_load_zero: assert property (
        @(posedge clk) disable iff (1'b0) (!clr && !pr && ena && !d) |=> (q == 1'b0)
    );

endmodule