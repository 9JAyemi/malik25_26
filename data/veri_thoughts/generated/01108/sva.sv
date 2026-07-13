module var14_multi_sva (
    input logic clk,
    input logic A, B, C, D, E, F, G, H, I, J, K, L, M, N,
    input logic valid
);
    // Recompute DUT combinational logic locally for checking
    wire [7:0] min_value  = 8'd120;
    wire [7:0] max_weight = 8'd60;
    wire [7:0] max_volume = 8'd60;

    wire [7:0] total_value =
          A * 8'd4
        + B * 8'd8
        + C * 8'd0
        + D * 8'd20
        + E * 8'd10
        + F * 8'd12
        + G * 8'd18
        + H * 8'd14
        + I * 8'd6
        + J * 8'd15
        + K * 8'd30
        + L * 8'd8
        + M * 8'd16
        + N * 8'd18;

    wire [7:0] total_weight =
          A * 8'd28
        + B * 8'd8
        + C * 8'd27
        + D * 8'd18
        + E * 8'd27
        + F * 8'd28
        + G * 8'd6
        + H * 8'd1
        + I * 8'd20
        + J * 8'd0
        + K * 8'd5
        + L * 8'd13
        + M * 8'd8
        + N * 8'd14;

    wire [7:0] total_volume =
          A * 8'd27
        + B * 8'd27
        + C * 8'd4
        + D * 8'd4
        + E * 8'd0
        + F * 8'd24
        + G * 8'd4
        + H * 8'd20
        + I * 8'd12
        + J * 8'd15
        + K * 8'd5
        + L * 8'd2
        + M * 8'd9
        + N * 8'd28;

    // valid matches the defined threshold comparison of totals
    check_valid_definition: assert property (
        @(posedge clk) valid == ((total_value >= min_value) && (total_weight <= max_weight) && (total_volume <= max_volume))
    );

    // Total value never exceeds sum of its coefficients (179)
    check_total_value_bound: assert property (
        @(posedge clk) total_value <= 8'd179
    );

    // Total weight never exceeds sum of its coefficients (203)
    check_total_weight_bound: assert property (
        @(posedge clk) total_weight <= 8'd203
    );

    // Total volume never exceeds sum of its coefficients (181)
    check_total_volume_bound: assert property (
        @(posedge clk) total_volume <= 8'd181
    );

    // All-zero inputs imply invalid (value too low)
    check_all_zero_implies_not_valid: assert property (
        @(posedge clk) (A==1'b0 && B==1'b0 && C==1'b0 && D==1'b0 && E==1'b0 && F==1'b0 && G==1'b0 &&
                        H==1'b0 && I==1'b0 && J==1'b0 && K==1'b0 && L==1'b0 && M==1'b0 && N==1'b0)
                        |-> (valid == 1'b0)
    );

    // Changing only C does not affect total_value (C's value coefficient is 0)
    check_c_change_no_value_effect: assert property (
        @(posedge clk) ($changed(C) && $stable({A,B,D,E,F,G,H,I,J,K,L,M,N}))
        |-> (total_value == $past(total_value))
    );

    // Changing only J does not affect total_weight (J's weight coefficient is 0)
    check_j_change_no_weight_effect: assert property (
        @(posedge clk) ($changed(J) && $stable({A,B,C,D,E,F,G,H,I,K,L,M,N}))
        |-> (total_weight == $past(total_weight))
    );

    // Changing only E does not affect total_volume (E's volume coefficient is 0)
    check_e_change_no_volume_effect: assert property (
        @(posedge clk) ($changed(E) && $stable({A,B,C,D,F,G,H,I,J,K,L,M,N}))
        |-> (total_volume == $past(total_volume))
    );

    // Rising A increases totals by its coefficients
    check_a_rise_increments_totals: assert property (
        @(posedge clk) ($rose(A) && $stable({B,C,D,E,F,G,H,I,J,K,L,M,N}))
        |-> ( (total_value  == $past(total_value)  + 8'd4)
           && (total_weight == $past(total_weight) + 8'd28)
           && (total_volume == $past(total_volume) + 8'd27) )
    );

    // Falling A decreases totals by its coefficients
    check_a_fall_decrements_totals: assert property (
        @(posedge clk) ($fell(A) && $stable({B,C,D,E,F,G,H,I,J,K,L,M,N}))
        |-> ( (total_value  == $past(total_value)  - 8'd4)
           && (total_weight == $past(total_weight) - 8'd28)
           && (total_volume == $past(total_volume) - 8'd27) )
    );

    // Rising K increases totals by its coefficients
    check_k_rise_increments_totals: assert property (
        @(posedge clk) ($rose(K) && $stable({A,B,C,D,E,F,G,H,I,J,L,M,N}))
        |-> ( (total_value  == $past(total_value)  + 8'd30)
           && (total_weight == $past(total_weight) + 8'd5)
           && (total_volume == $past(total_volume) + 8'd5) )
    );

    // Falling K decreases totals by its coefficients
    check_k_fall_decrements_totals: assert property (
        @(posedge clk) ($fell(K) && $stable({A,B,C,D,E,F,G,H,I,J,L,M,N}))
        |-> ( (total_value  == $past(total_value)  - 8'd30)
           && (total_weight == $past(total_weight) - 8'd5)
           && (total_volume == $past(total_volume) - 8'd5) )
    );

    // Rising J increases value and volume by 15 and keeps weight unchanged
    check_j_rise_effects: assert property (
        @(posedge clk) ($rose(J) && $stable({A,B,C,D,E,F,G,H,I,K,L,M,N}))
        |-> ( (total_value  == $past(total_value)  + 8'd15)
           && (total_weight == $past(total_weight) + 8'd0)
           && (total_volume == $past(total_volume) + 8'd15) )
    );

    // Falling J decreases value and volume by 15 and keeps weight unchanged
    check_j_fall_effects: assert property (
        @(posedge clk) ($fell(J) && $stable({A,B,C,D,E,F,G,H,I,K,L,M,N}))
        |-> ( (total_value  == $past(total_value)  - 8'd15)
           && (total_weight == $past(total_weight) - 8'd0)
           && (total_volume == $past(total_volume) - 8'd15) )
    );
endmodule