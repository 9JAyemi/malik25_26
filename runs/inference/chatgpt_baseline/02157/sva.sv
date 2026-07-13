module custom_module_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1
);
    // No clock or reset in RTL; pure combinational. Sample on posedge of A1.
    // X implements (A1 ^ A2) & B1.
    // Functional equivalence to the RTL expression.
    check_function_equivalence: assert property (
        @(posedge A1) X == ((A1 ^ A2) & B1)
    );
    // B1 low masks X to 0.
    check_mask_zero_when_B1_low: assert property (
        @(posedge A1) (B1 == 1'b0) |-> (X == 1'b0)
    );
    // When B1 is high, X equals A1 XOR A2.
    check_equals_xor_when_B1_high: assert property (
        @(posedge A1) (B1 == 1'b1) |-> (X == (A1 ^ A2))
    );
    // If X is high, then B1 is high and A1 != A2.
    check_x_high_implies_conditions: assert property (
        @(posedge A1) X |-> (B1 && (A1 ^ A2))
    );
    // With B1 high and A1 == A2, X must be 0.
    check_low_when_equal_inputs_and_enabled: assert property (
        @(posedge A1) (B1 && (A1 == A2)) |-> (X == 1'b0)
    );
    // With B1 high and A1 != A2, X must be 1.
    check_high_when_unequal_inputs_and_enabled: assert property (
        @(posedge A1) (B1 && (A1 != A2)) |-> (X == 1'b1)
    );
    // Sum-of-products equivalence for XOR gating.
    check_sop_equivalence: assert property (
        @(posedge A1) X == ((A1 & ~A2 & B1) | (~A1 & A2 & B1))
    );
    // Enabled case: A1=0,A2=0 -> X=0.
    check_case_enabled_A1_0_A2_0_zero: assert property (
        @(posedge A1) (B1 && ~A1 && ~A2) |-> (X == 1'b0)
    );
    // Enabled case: A1=1,A2=1 -> X=0.
    check_case_enabled_A1_1_A2_1_zero: assert property (
        @(posedge A1) (B1 && A1 && A2) |-> (X == 1'b0)
    );
    // Enabled case: A1=0,A2=1 -> X=1.
    check_case_enabled_A1_0_A2_1_one: assert property (
        @(posedge A1) (B1 && ~A1 && A2) |-> (X == 1'b1)
    );
endmodule