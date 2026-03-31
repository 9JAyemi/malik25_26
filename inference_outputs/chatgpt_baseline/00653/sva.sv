module and4_sva (
    input logic clk,     // Sampling clock for assertions (DUT has no clock)
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X,
    input logic and0_out,
    input logic and1_out
);
    // DUT has no reset; purely combinational 4-input AND built from 2-input ANDs.

    // and0_out must be 1 when both A and B are 1.
    check_and0_high_when_A_and_B_high: assert property (
        @(posedge clk) (A && B) |-> (and0_out == 1'b1)
    );

    // and0_out must be 0 when either A or B is 0.
    check_and0_low_when_A_or_B_low: assert property (
        @(posedge clk) ((!A) || (!B)) |-> (and0_out == 1'b0)
    );

    // and1_out must be 1 when both C and D are 1.
    check_and1_high_when_C_and_D_high: assert property (
        @(posedge clk) (C && D) |-> (and1_out == 1'b1)
    );

    // and1_out must be 0 when either C or D is 0.
    check_and1_low_when_C_or_D_low: assert property (
        @(posedge clk) ((!C) || (!D)) |-> (and1_out == 1'b0)
    );

    // X must be 1 when both sub-AND outputs are 1.
    check_X_high_when_subands_high: assert property (
        @(posedge clk) (and0_out && and1_out) |-> (X == 1'b1)
    );

    // X must be 0 when either sub-AND output is 0.
    check_X_low_when_any_suband_low: assert property (
        @(posedge clk) ((!and0_out) || (!and1_out)) |-> (X == 1'b0)
    );

    // X must be 1 when all four inputs are 1.
    check_X_high_when_all_inputs_high: assert property (
        @(posedge clk) (A && B && C && D) |-> (X == 1'b1)
    );

    // X must be 0 when any input is 0.
    check_X_low_when_any_input_low: assert property (
        @(posedge clk) ((!A) || (!B) || (!C) || (!D)) |-> (X == 1'b0)
    );

    // and0_out being 1 implies both A and B are 1.
    check_and0_high_implies_A_and_B_high: assert property (
        @(posedge clk) and0_out |-> (A && B)
    );

    // and1_out being 1 implies both C and D are 1.
    check_and1_high_implies_C_and_D_high: assert property (
        @(posedge clk) and1_out |-> (C && D)
    );

endmodule