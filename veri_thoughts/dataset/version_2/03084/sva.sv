module MUX_4_1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);

    // S low selects A.
    check_select_low_routes_a: assert property (
        @(posedge clk) (S === 1'b0) |-> (Y === A)
    );

    // S high selects B.
    check_select_high_routes_b: assert property (
        @(posedge clk) (S === 1'b1) |-> (Y === B)
    );

    // A selected path is reflected when A changes.
    check_selected_a_change_reflected: assert property (
        @(posedge clk) ($stable(S) && (S === 1'b0) && $changed(A)) |-> (Y === A)
    );

    // B selected path is reflected when B changes.
    check_selected_b_change_reflected: assert property (
        @(posedge clk) ($stable(S) && (S === 1'b1) && $changed(B)) |-> (Y === B)
    );

    // A is ignored when S stays high and B is stable.
    check_unselected_a_no_effect_when_s_high: assert property (
        @(posedge clk) ($stable(S) && (S === 1'b1) && $changed(A) && $stable(B)) |-> $stable(Y)
    );

    // B is ignored when S stays low and A is stable.
    check_unselected_b_no_effect_when_s_low: assert property (
        @(posedge clk) ($stable(S) && (S === 1'b0) && $changed(B) && $stable(A)) |-> $stable(Y)
    );

    // Rising select makes the output follow B.
    check_select_rise_routes_b: assert property (
        @(posedge clk) $rose(S) |-> (Y === B)
    );

    // Falling select makes the output follow A.
    check_select_fall_routes_a: assert property (
        @(posedge clk) $fell(S) |-> (Y === A)
    );

    // Stable inputs imply a stable output.
    check_stable_inputs_stable_output: assert property (
        @(posedge clk) $stable({A, B, S}) |-> $stable(Y)
    );

endmodule