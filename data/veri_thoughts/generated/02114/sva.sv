module mux_2to1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic out
);
    // Mux function: out equals a when sel==0, else equals b.
    check_mux_function: assert property (
        @(posedge clk) disable iff (1'b0) out == (sel ? b : a)
    );

    // When sel is 0, out must match a.
    check_sel0_routes_a: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 1'b0) |-> (out == a)
    );

    // When sel is 1, out must match b.
    check_sel1_routes_b: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 1'b1) |-> (out == b)
    );

    // If both inputs are equal, out must equal that value regardless of sel.
    check_equal_inputs_pass_through: assert property (
        @(posedge clk) disable iff (1'b0) (a == b) |-> (out == a)
    );
endmodule