module Select_AB_sva (
    input logic clk,
    input logic in_select,
    input logic in1,
    input logic in2,
    input logic A,
    input logic B
);

    // A matches the RTL mux expression.
    check_a_function: assert property (
        @(posedge clk) A === ((in_select == 1'b0) ? in2 : in1)
    );

    // B matches the RTL mux expression.
    check_b_function: assert property (
        @(posedge clk) B === ((in_select == 1'b0) ? in1 : in2)
    );

    // When select is low, A routes in2 and B routes in1.
    check_select_low_routes_outputs: assert property (
        @(posedge clk) (in_select === 1'b0) |-> ((A === in2) && (B === in1))
    );

    // When select is high, A routes in1 and B routes in2.
    check_select_high_routes_outputs: assert property (
        @(posedge clk) (in_select === 1'b1) |-> ((A === in1) && (B === in2))
    );

    // Equal inputs force both outputs to the same value.
    check_equal_inputs_produce_equal_outputs: assert property (
        @(posedge clk) (in1 === in2) |-> ((A === in1) && (B === in1))
    );

    // Stable inputs keep both outputs stable at the sampling edge.
    check_stable_inputs_keep_outputs_stable: assert property (
        @(posedge clk) ($stable(in_select) && $stable(in1) && $stable(in2)) |-> ($stable(A) && $stable(B))
    );

endmodule