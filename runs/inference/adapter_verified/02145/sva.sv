module mux_2_to_1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic out
);

// When sel is 0, out must equal a.
    check_sel0_routes_a: assert property (
        @(posedge clk) (sel == 1'b0) |-> (out == a)
    );

// When sel is 1, out must equal b.
    check_sel1_routes_b: assert property (
        @(posedge clk) (sel == 1'b1) |-> (out == b)
    );

// When a and b are equal, out must equal that value regardless of sel.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (a == b) |-> (out == a)
    );

// A rising sel must make out equal b on the next cycle.
    check_sel_rise_selects_b: assert property (
        @(posedge clk) $rose(sel) |=> (out == b)
    );

// A falling sel must make out equal a on the next cycle.
    check_sel_fall_selects_a: assert property (
        @(posedge clk) $fell(sel) |=> (out == a)
    );

endmodule
