module counter_sva (
    input logic clk,
    input logic reset,
    input logic in,
    input logic p,
    input logic [4:0] r
);
    // Reset drives r to 0 on the following clock.
    reset_clears_r: assert property (
        @(posedge clk) reset |-> (r == 5'd0)
    );

    // During reset, p must be 0.
    reset_drives_p_low: assert property (
        @(posedge clk) reset |-> (p == 1'b0)
    );

    // p is the combinational comparison (r == 20).
    p_matches_r_eq_20: assert property (
        @(posedge clk) disable iff (reset) p == (r == 5'd20)
    );

    // Exact next-state function for r; allow escape if reset rises between cycles.
    exact_next_state: assert property (
        @(posedge clk) disable iff (reset)
            1 |=> ($rose(reset) || (r == (in ? 5'd1 : ($past(r) != 5'd0 ? $past(r) + 5'd1 : $past(r)))))
    );

    // If previous r was nonzero and in is 0 now, r increments by 1 (mod 32).
    nonzero_increments_when_no_in: assert property (
        @(posedge clk) disable iff (reset)
            1 |=> ($rose(reset) || in || ($past(r) == 5'd0) || (r == $past(r) + 5'd1))
    );

    // If previous r was zero and in is 0 now, r stays at 0.
    zero_holds_when_no_in: assert property (
        @(posedge clk) disable iff (reset)
            1 |=> ($rose(reset) || in || ($past(r) != 5'd0) || (r == 5'd0))
    );

    // If in is 1 now, r is 1 now (assignment priority to 'in').
    in_forces_r_one: assert property (
        @(posedge clk) disable iff (reset)
            1 |=> ($rose(reset) || !in || (r == 5'd1))
    );

    // When previous r was 31 and in is 0 now, r wraps to 0.
    wrap_31_to_0: assert property (
        @(posedge clk) disable iff (reset)
            1 |=> ($rose(reset) || in || ($past(r) != 5'd31) || (r == 5'd0))
    );
endmodule