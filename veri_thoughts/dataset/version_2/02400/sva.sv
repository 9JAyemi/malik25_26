module mux2to1_sva (
    input logic clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic sel,
    input logic [31:0] c
);
    // Mux output must equal selected input.
    check_mux_function: assert property (
        @(posedge clk) c == (sel ? b : a)
    );

    // When sel==0, output equals a.
    check_sel0_path: assert property (
        @(posedge clk) (sel == 1'b0) |-> (c == a)
    );

    // When sel==1, output equals b.
    check_sel1_path: assert property (
        @(posedge clk) (sel == 1'b1) |-> (c == b)
    );

    // If inputs are equal, output equals that value regardless of sel.
    check_equal_inputs_force_equal_output: assert property (
        @(posedge clk) (a == b) |-> (c == a)
    );

    // If output differs from a, selection must be b and b must differ from a.
    check_output_diff_from_a_implies_select_b: assert property (
        @(posedge clk) (c != a) |-> (sel && (b != a))
    );

    // If output differs from b, selection must be a and a must differ from b.
    check_output_diff_from_b_implies_select_a: assert property (
        @(posedge clk) (c != b) |-> (!sel && (a != b))
    );
endmodule