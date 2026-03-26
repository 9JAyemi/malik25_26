module MUX2X1_sva (
    input logic clk,
    input logic in0,
    input logic in1,
    input logic sel,
    input logic out
);

    // Out must match the mux RTL equation.
    check_mux_truth_table: assert property (
        @(posedge clk) out === ((sel == 1'b0) ? in0 : in1)
    );

    // Select low routes in0 to out.
    check_sel_zero_routes_in0: assert property (
        @(posedge clk) (sel === 1'b0) |-> (out === in0)
    );

    // Select high routes in1 to out.
    check_sel_one_routes_in1: assert property (
        @(posedge clk) (sel === 1'b1) |-> (out === in1)
    );

    // Equal data inputs force the same sampled output.
    check_equal_inputs_force_output: assert property (
        @(posedge clk) (in0 === in1) |-> (out === in0)
    );

    // Stable inputs keep the sampled output stable.
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge clk) $stable({in0, in1, sel}) |-> $stable(out)
    );

endmodule