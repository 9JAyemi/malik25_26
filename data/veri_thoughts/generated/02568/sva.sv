module custom_or_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic out
);
    // Output equals (A | B) & C.
    check_function_equivalence: assert property (
        @(posedge clk) out == ((A | B) & C)
    );

    // If out is HIGH, C must be HIGH.
    check_out_implies_C: assert property (
        @(posedge clk) out |-> (C == 1'b1)
    );

    // If C is LOW, out must be LOW.
    check_out_zero_when_C_zero: assert property (
        @(posedge clk) (C == 1'b0) |-> (out == 1'b0)
    );

    // If A and B are both LOW, out must be LOW.
    check_out_zero_when_A_and_B_zero: assert property (
        @(posedge clk) (!A && !B) |-> (out == 1'b0)
    );

    // If C is HIGH and (A or B) is HIGH, out must be HIGH.
    check_out_one_when_C_and_AorB_one: assert property (
        @(posedge clk) (C && (A || B)) |-> (out == 1'b1)
    );

    // With inputs stable, output remains stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable(A) && $stable(B) && $stable(C) |-> $stable(out)
    );

    // A rising out requires C HIGH.
    check_out_rise_requires_C_high: assert property (
        @(posedge clk) $rose(out) |-> (C == 1'b1)
    );

    // A rising out requires A or B HIGH.
    check_out_rise_requires_A_or_B_high: assert property (
        @(posedge clk) $rose(out) |-> (A || B)
    );

    // A falling out implies C LOW or both A and B LOW.
    check_out_fall_requires_inputs_low: assert property (
        @(posedge clk) $fell(out) |-> (!C || (!A && !B))
    );

    // If C rises and (A or B) is HIGH, out must rise.
    check_out_rises_with_C_when_enabled: assert property (
        @(posedge clk) $rose(C) && (A || B) |-> $rose(out)
    );
endmodule