module logic_gates_sva (
    input logic in1,
    input logic in2,
    input logic out,
    input logic and_out,
    input logic or_out,
    input logic not_out,
    input logic xor_out,
    input logic xnor_out
);
    ///// Functional correctness of gates /////
    // AND gate output equals in1 & in2.
    check_and_gate_function: assert property (
        @(posedge in1 or negedge in1 or posedge in2 or negedge in2) and_out == (in1 & in2)
    );
    // OR gate output equals in1 | in2.
    check_or_gate_function: assert property (
        @(posedge in1 or negedge in1 or posedge in2 or negedge in2) or_out == (in1 | in2)
    );
    // NOT gate output equals ~in1.
    check_not_gate_function: assert property (
        @(posedge in1 or negedge in1 or posedge in2 or negedge in2) not_out == (~in1)
    );
    // XOR gate output equals in1 ^ in2.
    check_xor_gate_function: assert property (
        @(posedge in1 or negedge in1 or posedge in2 or negedge in2) xor_out == (in1 ^ in2)
    );
    // XNOR gate output equals in1 ~^ in2.
    check_xnor_gate_function: assert property (
        @(posedge in1 or negedge in1 or posedge in2 or negedge in2) xnor_out == (in1 ~^ in2)
    );

    ///// Output assignment /////
    // out drives the AND gate result.
    check_out_is_and: assert property (
        @(posedge in1 or negedge in1 or posedge in2 or negedge in2) out == and_out
    );

    ///// Derived AND behavior on out /////
    // If any input is LOW, out must be LOW.
    check_out_low_when_any_low: assert property (
        @(posedge in1 or negedge in1 or posedge in2 or negedge in2) ((in1 == 1'b0) || (in2 == 1'b0)) |-> (out == 1'b0)
    );
    // If both inputs are HIGH, out must be HIGH.
    check_out_high_when_both_high: assert property (
        @(posedge in1 or negedge in1 or posedge in2 or negedge in2) ((in1 == 1'b1) && (in2 == 1'b1)) |-> (out == 1'b1)
    );
    // out HIGH implies both inputs are HIGH.
    check_out_high_implies_both_high: assert property (
        @(posedge in1 or negedge in1 or posedge in2 or negedge in2) (out == 1'b1) |-> ((in1 == 1'b1) && (in2 == 1'b1))
    );
    // out falling edge implies at least one input is LOW.
    check_out_fall_requires_any_low: assert property (
        @(posedge in1 or negedge in1 or posedge in2 or negedge in2) $fell(out) |-> ((in1 == 1'b0) || (in2 == 1'b0))
    );
endmodule