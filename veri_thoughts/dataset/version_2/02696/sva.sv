module sky130_fd_sc_ms__or4_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);
    // X must be 1 if any input is 1.
    check_x_high_if_any_input_high: assert property (
        @(posedge clk) ((A===1'b1) || (B===1'b1) || (C===1'b1) || (D===1'b1)) |-> (X===1'b1)
    );

    // X must be 0 if all inputs are 0.
    check_x_low_if_all_inputs_low: assert property (
        @(posedge clk) ((A===1'b0) && (B===1'b0) && (C===1'b0) && (D===1'b0)) |-> (X===1'b0)
    );

    // When B,C,D are 0, X equals A.
    check_pass_A_when_others_low: assert property (
        @(posedge clk) ((B===1'b0) && (C===1'b0) && (D===1'b0)) |-> (X === A)
    );

    // When A,C,D are 0, X equals B.
    check_pass_B_when_others_low: assert property (
        @(posedge clk) ((A===1'b0) && (C===1'b0) && (D===1'b0)) |-> (X === B)
    );

    // When A,B,D are 0, X equals C.
    check_pass_C_when_others_low: assert property (
        @(posedge clk) ((A===1'b0) && (B===1'b0) && (D===1'b0)) |-> (X === C)
    );

    // When A,B,C are 0, X equals D.
    check_pass_D_when_others_low: assert property (
        @(posedge clk) ((A===1'b0) && (B===1'b0) && (C===1'b0)) |-> (X === D)
    );

    // A rising edge on X implies at least one input is 1 now.
    check_x_rise_requires_some_input_high: assert property (
        @(posedge clk) $rose(X) |-> ((A===1'b1) || (B===1'b1) || (C===1'b1) || (D===1'b1))
    );

    // A falling edge on X implies all inputs are 0 now.
    check_x_fall_requires_all_inputs_low: assert property (
        @(posedge clk) $fell(X) |-> ((A===1'b0) && (B===1'b0) && (C===1'b0) && (D===1'b0))
    );

    // If A rises while others are 0 in both cycles, X must rise.
    check_a_rise_causes_x_rise_when_others_low: assert property (
        @(posedge clk) $rose(A) && $past((B===1'b0)&&(C===1'b0)&&(D===1'b0)) && ((B===1'b0)&&(C===1'b0)&&(D===1'b0)) |-> $rose(X)
    );

    // If A falls while others are 0 in both cycles, X must fall.
    check_a_fall_causes_x_fall_when_others_low: assert property (
        @(posedge clk) $fell(A) && $past((B===1'b0)&&(C===1'b0)&&(D===1'b0)) && ((B===1'b0)&&(C===1'b0)&&(D===1'b0)) |-> $fell(X)
    );
endmodule