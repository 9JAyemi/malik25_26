module adder_4bit_sva (
    input logic clk,           // External clock for sampling assertions
    input logic [3:0] A,
    input logic [3:0] B,
    input logic S,
    input logic [3:0] C
);
    ///// Functional correctness /////
    // When S==0, C must equal A + B (4-bit wrap).
    check_add_mode_correct: assert property (
        @(posedge clk) (S == 1'b0) |-> (C == (A + B))
    );
    // When S==1, C must equal A - B (4-bit wrap).
    check_sub_mode_correct: assert property (
        @(posedge clk) (S == 1'b1) |-> (C == (A - B))
    );

    ///// Determinism and stability /////
    // If inputs A,B,S are unchanged from last cycle, C must be unchanged.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) ({A,B,S} == $past({A,B,S})) |-> (C == $past(C))
    );

    ///// X-propagation /////
    // If A,B,S are all known (no X/Z), then C must be known.
    check_known_output_with_known_inputs: assert property (
        @(posedge clk) (!$isunknown({A,B,S})) |-> (!$isunknown(C))
    );

    ///// Algebraic identities (direct consequences of + and -) /////
    // In add mode, adding zero B passes A through.
    check_add_zero_B_passthru: assert property (
        @(posedge clk) (S == 1'b0 && B == 4'h0) |-> (C == A)
    );
    // In add mode, adding zero A passes B through.
    check_add_zero_A_passthru: assert property (
        @(posedge clk) (S == 1'b0 && A == 4'h0) |-> (C == B)
    );
    // In sub mode, subtracting zero B passes A through.
    check_sub_zero_B_passthru: assert property (
        @(posedge clk) (S == 1'b1 && B == 4'h0) |-> (C == A)
    );
    // In sub mode, subtracting equal operands yields zero.
    check_sub_equal_inputs_zero: assert property (
        @(posedge clk) (S == 1'b1 && A == B) |-> (C == 4'h0)
    );
endmodule