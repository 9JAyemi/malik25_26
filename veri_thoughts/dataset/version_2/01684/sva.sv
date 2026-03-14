module mux_2to1_with_control_sva (
    input logic clk,   // sampling clock for assertions
    input logic A,
    input logic B,
    input logic Sel,
    input logic Out
);
    // Out equals (~Sel & A) | Sel (functional reduction of the RTL).
    check_out_eq_boolean_function: assert property (
        @(posedge clk) Out == ((~Sel & A) | Sel)
    );

    // When Sel is LOW, Out equals A.
    check_out_eq_a_when_sel_low: assert property (
        @(posedge clk) (Sel == 1'b0) |-> (Out == A)
    );

    // When Sel is HIGH, Out must be HIGH.
    check_out_high_when_sel_high: assert property (
        @(posedge clk) (Sel == 1'b1) |-> (Out == 1'b1)
    );

    // If Out is LOW, both Sel and A are LOW.
    check_out_low_implies_sel_and_a_low: assert property (
        @(posedge clk) (Out == 1'b0) |-> ((Sel == 1'b0) && (A == 1'b0))
    );

    // A rise with Sel LOW sets Out HIGH.
    check_a_rise_sets_out_when_sel_low: assert property (
        @(posedge clk) ((Sel == 1'b0) && $rose(A)) |-> (Out == 1'b1)
    );

    // A fall with Sel LOW clears Out LOW.
    check_a_fall_clears_out_when_sel_low: assert property (
        @(posedge clk) ((Sel == 1'b0) && $fell(A)) |-> (Out == 1'b0)
    );

    // Sel rising forces Out HIGH immediately.
    check_sel_rise_forces_out_high: assert property (
        @(posedge clk) $rose(Sel) |-> (Out == 1'b1)
    );

    // Sel falling makes Out equal to A.
    check_sel_fall_makes_out_equal_a: assert property (
        @(posedge clk) $fell(Sel) |-> (Out == A)
    );

    // Out can only rise if A or Sel is HIGH.
    check_out_rise_requires_a_or_sel_high: assert property (
        @(posedge clk) $rose(Out) |-> ((A == 1'b1) || (Sel == 1'b1))
    );

    // Out can only fall if both A and Sel are LOW.
    check_out_fall_requires_a_and_sel_low: assert property (
        @(posedge clk) $fell(Out) |-> ((A == 1'b0) && (Sel == 1'b0))
    );

    // Changes on B alone cannot change Out (B is functionally irrelevant).
    check_b_independence_of_out: assert property (
        @(posedge clk) ($changed(B) && $stable(A) && $stable(Sel)) |-> $stable(Out)
    );
endmodule