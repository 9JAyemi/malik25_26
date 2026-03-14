module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [99:0] in,
    input logic [7:0] a, b, c, d,
    input logic [7:0] min,
    input logic out
);

    ///// Priority encoder + mux behavior observed at top /////
    // When a is strictly greater than b,c,d, min selects a.
    check_min_select_a: assert property (
        @(posedge clk) disable iff (reset) ((a > b) && (a > c) && (a > d)) |-> (min == a)
    );
    // When a is not strictly max and b > c and b > d, min selects b.
    check_min_select_b: assert property (
        @(posedge clk) disable iff (reset) (!( (a > b) && (a > c) && (a > d) ) && (b > c) && (b > d)) |-> (min == b)
    );
    // When a,b conditions fail and c > d, min selects c.
    check_min_select_c: assert property (
        @(posedge clk) disable iff (reset) (!( (a > b) && (a > c) && (a > d) ) && !((b > c) && (b > d)) && (c > d)) |-> (min == c)
    );
    // When none of the above, min selects d.
    check_min_select_d: assert property (
        @(posedge clk) disable iff (reset) (!( (a > b) && (a > c) && (a > d) ) && !((b > c) && (b > d)) && !(c > d)) |-> (min == d)
    );
    // min must equal one of a,b,c,d.
    check_min_is_one_of_inputs: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |-> ((min == a) || (min == b) || (min == c) || (min == d))
    );
    // If min == a then a is strictly greater than b,c,d.
    check_min_implies_a_cond: assert property (
        @(posedge clk) disable iff (reset) (min == a) |-> ((a > b) && (a > c) && (a > d))
    );
    // If min == b then a is not strictly max and b > c and b > d.
    check_min_implies_b_cond: assert property (
        @(posedge clk) disable iff (reset) (min == b) |-> (!( (a > b) && (a > c) && (a > d) ) && (b > c) && (b > d))
    );
    // If min == c then prior conditions fail and c > d.
    check_min_implies_c_cond: assert property (
        @(posedge clk) disable iff (reset) (min == c) |-> (!( (a > b) && (a > c) && (a > d) ) && !((b > c) && (b > d)) && (c > d))
    );
    // If min == d then none of the prior conditions hold.
    check_min_implies_d_cond: assert property (
        @(posedge clk) disable iff (reset) (min == d) |-> (!( (a > b) && (a > c) && (a > d) ) && !((b > c) && (b > d)) && !(c > d))
    );

    ///// comb_logic contribution to out observed at top /////
    // out equals OR of reductions (&, |, ^) of in[49:0].
    check_out_function: assert property (
        @(posedge clk) disable iff (reset) out == ((|in[49:0]) | (&in[49:0]) | (^in[49:0]))
    );
    // Changing only in[99:50] does not change out.
    check_out_independent_upper: assert property (
        @(posedge clk) disable iff (reset) ($changed(in[99:50]) && $stable(in[49:0])) |-> $stable(out)
    );
    // Changes on in do not affect min when a,b,c,d are stable.
    check_min_independent_in: assert property (
        @(posedge clk) disable iff (reset) ($changed(in) && $stable({a,b,c,d})) |-> $stable(min)
    );

endmodule