module wordlib8__PPGen_1bit_sva (
    input logic CLK,
    input logic RESETn,
    input logic Double,
    input logic Negate,
    input logic Single,
    input logic Yi,
    input logic Yi_m1,
    input logic PPi
);
    ///// Combinational function checks /////
    // PPi equals ((Single & Yi) | (Double & Yi_m1)) XOR Negate.
    check_ppi_function: assert property (
        @(posedge CLK) disable iff (!RESETn)
        PPi == (((Single & Yi) | (Double & Yi_m1)) ^ Negate)
    );

    // When Negate is 0, PPi equals (Single & Yi) | (Double & Yi_m1).
    check_negate_low_direct: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (Negate == 1'b0) |-> (PPi == ((Single & Yi) | (Double & Yi_m1)))
    );

    // When Negate is 1, PPi equals inversion of (Single & Yi) | (Double & Yi_m1).
    check_negate_high_inverted: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (Negate == 1'b1) |-> (PPi == ~((Single & Yi) | (Double & Yi_m1)))
    );

    // If Single=0 and Double=0, PPi equals Negate.
    check_zero_controls_ppi_eq_negate: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((Single == 1'b0) && (Double == 1'b0)) |-> (PPi == Negate)
    );

    // If Yi=0 and Yi_m1=0, PPi equals Negate.
    check_zero_multiplicands_ppi_eq_negate: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((Yi == 1'b0) && (Yi_m1 == 1'b0)) |-> (PPi == Negate)
    );

    // With Negate=0 and at least one AND term true, PPi is 1.
    check_negate0_one_and1_ppi1: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (Negate == 1'b0) && (((Single & Yi) == 1'b1) || ((Double & Yi_m1) == 1'b1)) |-> (PPi == 1'b1)
    );

    // With Negate=0 and both AND terms false, PPi is 0.
    check_negate0_both_and0_ppi0: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (Negate == 1'b0) && (((Single & Yi) == 1'b0) && ((Double & Yi_m1) == 1'b0)) |-> (PPi == 1'b0)
    );

    // With Negate=1 and at least one AND term true, PPi is 0.
    check_negate1_one_and1_ppi0: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (Negate == 1'b1) && (((Single & Yi) == 1'b1) || ((Double & Yi_m1) == 1'b1)) |-> (PPi == 1'b0)
    );

    // With Negate=1 and both AND terms false, PPi is 1.
    check_negate1_both_and0_ppi1: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (Negate == 1'b1) && (((Single & Yi) == 1'b0) && ((Double & Yi_m1) == 1'b0)) |-> (PPi == 1'b1)
    );

    ///// Temporal consistency for pure combinational logic /////
    // If all inputs are stable, PPi must be stable.
    check_stable_inputs_stable_output: assert property (
        @(posedge CLK) disable iff (!RESETn)
        $stable(Double) && $stable(Negate) && $stable(Single) && $stable(Yi) && $stable(Yi_m1) |-> $stable(PPi)
    );

    // If only Negate toggles and others are stable, PPi toggles.
    check_negate_toggle_toggles_ppi: assert property (
        @(posedge CLK) disable iff (!RESETn)
        $changed(Negate) && $stable(Double) && $stable(Single) && $stable(Yi) && $stable(Yi_m1) |-> $changed(PPi)
    );
endmodule