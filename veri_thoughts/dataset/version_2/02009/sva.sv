module and_or_gate_fixed_sva (
    input logic clk,
    input logic i0,
    input logic i1,
    input logic i2,
    input logic i3,
    input logic i4,
    input logic i5,
    input logic o
);
    // Output equals the AND of all six inputs.
    check_and_equivalence: assert property (
        @(posedge clk) o == (i0 & i1 & i2 & i3 & i4 & i5)
    );

    // If o is HIGH, all inputs must be HIGH (same cycle).
    check_o_high_implies_all_high: assert property (
        @(posedge clk) o |=> (i0 & i1 & i2 & i3 & i4 & i5)
    );

    // If i0 is LOW, o must be LOW (same cycle).
    check_low_dominance_i0: assert property (
        @(posedge clk) (!i0) |=> (!o)
    );

    // If i1 is LOW, o must be LOW (same cycle).
    check_low_dominance_i1: assert property (
        @(posedge clk) (!i1) |=> (!o)
    );

    // If i2 is LOW, o must be LOW (same cycle).
    check_low_dominance_i2: assert property (
        @(posedge clk) (!i2) |=> (!o)
    );

    // If i3 is LOW, o must be LOW (same cycle).
    check_low_dominance_i3: assert property (
        @(posedge clk) (!i3) |=> (!o)
    );

    // If i4 is LOW, o must be LOW (same cycle).
    check_low_dominance_i4: assert property (
        @(posedge clk) (!i4) |=> (!o)
    );

    // If i5 is LOW, o must be LOW (same cycle).
    check_low_dominance_i5: assert property (
        @(posedge clk) (!i5) |=> (!o)
    );

    // If all inputs are HIGH, o must be HIGH (same cycle).
    check_all_high_implies_o_high: assert property (
        @(posedge clk) (i0 & i1 & i2 & i3 & i4 & i5) |=> o
    );
endmodule