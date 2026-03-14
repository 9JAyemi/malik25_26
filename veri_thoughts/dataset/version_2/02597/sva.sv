module and_gate_sva (
    input logic CLK,
    input logic a,
    input logic b,
    input logic out
);
    // Functional NOR relation: out equals ~(a | b).
    check_out_is_nor_ab: assert property (
        @(posedge CLK) out == ~(a | b)
    );

    // Out HIGH only when both inputs are LOW.
    check_out_high_only_when_both_low: assert property (
        @(posedge CLK) out |-> (!a && !b)
    );

    // If any input is HIGH, out must be LOW.
    check_any_input_high_forces_out_low: assert property (
        @(posedge CLK) (a || b) |-> (!out)
    );

    // If both inputs are LOW, out must be HIGH.
    check_both_low_implies_out_high: assert property (
        @(posedge CLK) (!a && !b) |-> out
    );
endmodule