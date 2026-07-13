module multiplier_module_sva (
    input logic clk,
    input logic reset,      // Active-high synchronous reset
    input logic [15:0] a,
    input logic [15:0] b,
    input logic [15:0] p
);
    // After any cycle with reset=1, p is 0 in the next cycle.
    check_reset_clears_p_next: assert property (
        @(posedge clk) disable iff (reset)
            $past(reset) |-> (p == 16'h0000)
    );

    // When prior cycle not in reset, p equals low 16 bits of a*b from prior cycle.
    check_registered_multiply_low16: assert property (
        @(posedge clk) disable iff (reset)
            !$past(reset) |-> (p == (($past(a) * $past(b)) [15:0]))
    );

    // If previous a was zero (and not in reset), p is zero now.
    check_zero_a_implies_zero_p: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(a) == 16'h0000)) |-> (p == 16'h0000)
    );

    // If previous b was zero (and not in reset), p is zero now.
    check_zero_b_implies_zero_p: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(b) == 16'h0000)) |-> (p == 16'h0000)
    );

    // If previous a was one (and not in reset), p equals previous b.
    check_one_a_passthrough_b: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(a) == 16'h0001)) |-> (p == $past(b))
    );

    // If previous b was one (and not in reset), p equals previous a.
    check_one_b_passthrough_a: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(b) == 16'h0001)) |-> (p == $past(a))
    );

    // If inputs are stable across the last and current cycle (and not in reset), p is stable into the next cycle.
    check_stable_inputs_imply_stable_p: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && !reset && ($past(a) == a) && ($past(b) == b)) |=> (p == $past(p))
    );
endmodule