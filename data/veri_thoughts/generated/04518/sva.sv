module var18_multi_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic F,
    input logic G,
    input logic H,
    input logic I,
    input logic J,
    input logic K,
    input logic L,
    input logic M,
    input logic N,
    input logic O,
    input logic P,
    input logic Q,
    input logic R,
    input logic valid
);

    // valid must match the combinational threshold expression.
    check_valid_matches_comb_logic: assert property (
        @(posedge clk)
        valid == (
            (((A * 9'd4)
            + (B * 9'd8)
            + (C * 9'd0)
            + (D * 9'd20)
            + (E * 9'd10)
            + (F * 9'd12)
            + (G * 9'd18)
            + (H * 9'd14)
            + (I * 9'd6)
            + (J * 9'd15)
            + (K * 9'd30)
            + (L * 9'd8)
            + (M * 9'd16)
            + (N * 9'd18)
            + (O * 9'd18)
            + (P * 9'd14)
            + (Q * 9'd7)
            + (R * 9'd7)) >= 9'd120)
            &&
            (((A * 9'd28)
            + (B * 9'd8)
            + (C * 9'd27)
            + (D * 9'd18)
            + (E * 9'd27)
            + (F * 9'd28)
            + (G * 9'd6)
            + (H * 9'd1)
            + (I * 9'd20)
            + (J * 9'd0)
            + (K * 9'd5)
            + (L * 9'd13)
            + (M * 9'd8)
            + (N * 9'd14)
            + (O * 9'd22)
            + (P * 9'd12)
            + (Q * 9'd23)
            + (R * 9'd26)) <= 9'd60)
            &&
            (((A * 9'd27)
            + (B * 9'd27)
            + (C * 9'd4)
            + (D * 9'd4)
            + (E * 9'd0)
            + (F * 9'd24)
            + (G * 9'd4)
            + (H * 9'd20)
            + (I * 9'd12)
            + (J * 9'd15)
            + (K * 9'd5)
            + (L * 9'd2)
            + (M * 9'd9)
            + (N * 9'd28)
            + (O * 9'd19)
            + (P * 9'd18)
            + (Q * 9'd30)
            + (R * 9'd12)) <= 9'd60)
        )
    );

    // valid can only be high when total value meets the minimum.
    check_valid_requires_min_value: assert property (
        @(posedge clk)
        valid |-> (
            ((A * 9'd4)
          + (B * 9'd8)
          + (C * 9'd0)
          + (D * 9'd20)
          + (E * 9'd10)
          + (F * 9'd12)
          + (G * 9'd18)
          + (H * 9'd14)
          + (I * 9'd6)
          + (J * 9'd15)
          + (K * 9'd30)
          + (L * 9'd8)
          + (M * 9'd16)
          + (N * 9'd18)
          + (O * 9'd18)
          + (P * 9'd14)
          + (Q * 9'd7)
          + (R * 9'd7)) >= 9'd120
        )
    );

    // valid can only be high when total weight is within the limit.
    check_valid_requires_max_weight: assert property (
        @(posedge clk)
        valid |-> (
            ((A * 9'd28)
          + (B * 9'd8)
          + (C * 9'd27)
          + (D * 9'd18)
          + (E * 9'd27)
          + (F * 9'd28)
          + (G * 9'd6)
          + (H * 9'd1)
          + (I * 9'd20)
          + (J * 9'd0)
          + (K * 9'd5)
          + (L * 9'd13)
          + (M * 9'd8)
          + (N * 9'd14)
          + (O * 9'd22)
          + (P * 9'd12)
          + (Q * 9'd23)
          + (R * 9'd26)) <= 9'd60
        )
    );

    // valid can only be high when total volume is within the limit.
    check_valid_requires_max_volume: assert property (
        @(posedge clk)
        valid |-> (
            ((A * 9'd27)
          + (B * 9'd27)
          + (C * 9'd4)
          + (D * 9'd4)
          + (E * 9'd0)
          + (F * 9'd24)
          + (G * 9'd4)
          + (H * 9'd20)
          + (I * 9'd12)
          + (J * 9'd15)
          + (K * 9'd5)
          + (L * 9'd2)
          + (M * 9'd9)
          + (N * 9'd28)
          + (O * 9'd19)
          + (P * 9'd18)
          + (Q * 9'd30)
          + (R * 9'd12)) <= 9'd60
        )
    );

    // valid must be high whenever all three constraints are satisfied.
    check_valid_asserts_when_all_constraints_met: assert property (
        @(posedge clk)
        (
            (((A * 9'd4)
            + (B * 9'd8)
            + (C * 9'd0)
            + (D * 9'd20)
            + (E * 9'd10)
            + (F * 9'd12)
            + (G * 9'd18)
            + (H * 9'd14)
            + (I * 9'd6)
            + (J * 9'd15)
            + (K * 9'd30)
            + (L * 9'd8)
            + (M * 9'd16)
            + (N * 9'd18)
            + (O * 9'd18)
            + (P * 9'd14)
            + (Q * 9'd7)
            + (R * 9'd7)) >= 9'd120)
            &&
            (((A * 9'd28)
            + (B * 9'd8)
            + (C * 9'd27)
            + (D * 9'd18)
            + (E * 9'd27)
            + (F * 9'd28)
            + (G * 9'd6)
            + (H * 9'd1)
            + (I * 9'd20)
            + (J * 9'd0)
            + (K * 9'd5)
            + (L * 9'd13)
            + (M * 9'd8)
            + (N * 9'd14)
            + (O * 9'd22)
            + (P * 9'd12)
            + (Q * 9'd23)
            + (R * 9'd26)) <= 9'd60)
            &&
            (((A * 9'd27)
            + (B * 9'd27)
            + (C * 9'd4)
            + (D * 9'd4)
            + (E * 9'd0)
            + (F * 9'd24)
            + (G * 9'd4)
            + (H * 9'd20)
            + (I * 9'd12)
            + (J * 9'd15)
            + (K * 9'd5)
            + (L * 9'd2)
            + (M * 9'd9)
            + (N * 9'd28)
            + (O * 9'd19)
            + (P * 9'd18)
            + (Q * 9'd30)
            + (R * 9'd12)) <= 9'd60)
        ) |-> valid
    );

    // If the item selections do not change, valid must not change.
    check_valid_stable_when_inputs_stable: assert property (
        @(posedge clk)
        $stable({A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R}) |-> $stable(valid)
    );

    // With no items selected, valid must be low.
    check_all_zero_selection_invalid: assert property (
        @(posedge clk)
        !(A || B || C || D || E || F || G || H || I || J || K || L || M || N || O || P || Q || R) |-> !valid
    );

endmodule