module velocityControlHdl_Clamp_block1_sva (
    input  logic CLK,
    input  logic signed [35:0] preSat,
    input  logic               saturated,
    input  logic signed [35:0] preIntegrator,
    input  logic               Clamp
);
    ///// Functional equivalence /////
    // Clamp equals saturated AND XNOR of (preIntegrator<=0) and (preSat<=0).
    check_clamp_function: assert property (
        @(posedge CLK) disable iff (1'b0)
        Clamp == (saturated && ((preIntegrator <= 36'sd0) == (preSat <= 36'sd0)))
    );

    ///// Implications of saturated /////
    // If not saturated, Clamp must be 0.
    check_not_saturated_clamp_zero: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!saturated) |-> (Clamp == 1'b0)
    );
    // If saturated and both inputs are <= 0, Clamp must be 1.
    check_sat_both_nonpos_implies_clamp: assert property (
        @(posedge CLK) disable iff (1'b0)
        (saturated && (preIntegrator <= 36'sd0) && (preSat <= 36'sd0)) |-> (Clamp == 1'b1)
    );
    // If saturated and both inputs are > 0, Clamp must be 1.
    check_sat_both_pos_implies_clamp: assert property (
        @(posedge CLK) disable iff (1'b0)
        (saturated && (preIntegrator > 36'sd0) && (preSat > 36'sd0)) |-> (Clamp == 1'b1)
    );
    // If saturated and the signs differ relative to zero, Clamp must be 0.
    check_sat_opposite_signs_implies_not_clamp: assert property (
        @(posedge CLK) disable iff (1'b0)
        (saturated && ((preIntegrator <= 36'sd0) != (preSat <= 36'sd0))) |-> (Clamp == 1'b0)
    );

    ///// Necessary conditions for Clamp high /////
    // If Clamp is 1, saturated must be 1.
    check_clamp_high_requires_saturated: assert property (
        @(posedge CLK) disable iff (1'b0)
        (Clamp == 1'b1) |-> (saturated == 1'b1)
    );
    // If Clamp is 1, (preIntegrator<=0) must equal (preSat<=0).
    check_clamp_high_requires_signs_equal: assert property (
        @(posedge CLK) disable iff (1'b0)
        (Clamp == 1'b1) |-> ((preIntegrator <= 36'sd0) == (preSat <= 36'sd0))
    );
endmodule