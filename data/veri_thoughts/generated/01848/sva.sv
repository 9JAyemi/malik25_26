module binary_adder_sva (
    input logic CLK,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic ctrl,
    input logic [3:0] sum,
    input logic cout
);
    // Combinational DUT with no reset/clock; assertions sample on CLK; ctrl=1: add, ctrl=0: pass-through.

    // Unified functional mapping for both modes.
    check_unified_function: assert property (
        @(posedge CLK) {cout, sum} == (ctrl ? (a + b + cin) : {cin, a})
    );

    // In pass-through mode, sum equals a.
    check_ctrl0_sum_passthrough: assert property (
        @(posedge CLK) (ctrl == 1'b0) |-> (sum == a)
    );

    // In pass-through mode, cout equals cin.
    check_ctrl0_cout_passthrough: assert property (
        @(posedge CLK) (ctrl == 1'b0) |-> (cout == cin)
    );

    // In add mode, concatenated outputs equal a + b + cin.
    check_ctrl1_add_concat: assert property (
        @(posedge CLK) (ctrl == 1'b1) |-> ({cout, sum} == (a + b + cin))
    );

    // In add mode with no carry, cout must be 0.
    check_ctrl1_no_carry_cout0: assert property (
        @(posedge CLK) (ctrl && !((a + b + cin)[4])) |-> (cout == 1'b0)
    );

    // In add mode with carry, cout must be 1.
    check_ctrl1_carry_cout1: assert property (
        @(posedge CLK) (ctrl && ((a + b + cin)[4])) |-> (cout == 1'b1)
    );

    // Pass-through mode: outputs ignore b changes (stable a,cin,ctrl implies stable outputs).
    check_ctrl0_ignores_b: assert property (
        @(posedge CLK) ((ctrl == 1'b0) && $stable(a) && $stable(cin) && $stable(ctrl)) |-> ($stable(sum) && $stable(cout))
    );

    // With all inputs stable, outputs remain stable.
    check_stable_outputs_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(a) && $stable(b) && $stable(cin) && $stable(ctrl)) |-> ($stable(sum) && $stable(cout))
    );

    // In pass-through mode, the pair {cout,sum} equals {cin,a}.
    check_ctrl0_pair_match: assert property (
        @(posedge CLK) (ctrl == 1'b0) |-> ({cout, sum} == {cin, a})
    );

    // In add mode, sum equals low 4 bits of a + b + cin.
    check_ctrl1_sum_lowbits: assert property (
        @(posedge CLK) (ctrl == 1'b1) |-> (sum == (a + b + cin)[3:0])
    );

endmodule