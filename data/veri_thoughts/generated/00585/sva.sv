module mux_2to1_sva (
    input logic clk,   // sampling clock for combinational DUT
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);
    // When S is 0, output must equal A.
    check_select0_routes_A: assert property (
        @(posedge clk) (S === 1'b0) |-> (Y === A)
    );

    // When S is 1, output must equal B.
    check_select1_routes_B: assert property (
        @(posedge clk) (S === 1'b1) |-> (Y === B)
    );

    // If A equals B, output must equal that common value.
    check_equal_inputs_pass_through: assert property (
        @(posedge clk) (A === B) |-> (Y === A)
    );

    // If S, A, and B are stable across a cycle, Y must be stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(S) && $stable(A) && $stable(B)) |-> $stable(Y)
    );

    // If Y changes, it must be due to S changing or the selected input changing.
    check_output_change_requires_cause: assert property (
        @(posedge clk) (!$stable(Y)) |-> ( !$stable(S)
                                        || (S === 1'b0 && !$stable(A))
                                        || (S === 1'b1 && !$stable(B)) )
    );

    // With S held at 0, a change on A must be reflected on Y at the next sample.
    check_s0_a_change_updates_y: assert property (
        @(posedge clk) (S === 1'b0 && $past(S) === 1'b0 && (A !== $past(A))) |-> (Y === A)
    );

    // With S held at 1, a change on B must be reflected on Y at the next sample.
    check_s1_b_change_updates_y: assert property (
        @(posedge clk) (S === 1'b1 && $past(S) === 1'b1 && (B !== $past(B))) |-> (Y === B)
    );

    // On a rising edge of S, output must equal B.
    check_sel_rise_selects_B: assert property (
        @(posedge clk) $rose(S) |-> (Y === B)
    );

    // On a falling edge of S, output must equal A.
    check_sel_fall_selects_A: assert property (
        @(posedge clk) $fell(S) |-> (Y === A)
    );

    // With S held at 0 and A stable, Y must remain stable (B changes cannot affect Y).
    check_irrelevant_input_no_effect_s0: assert property (
        @(posedge clk) (S === 1'b0 && $past(S) === 1'b0 && $stable(A)) |-> $stable(Y)
    );

    // With S held at 1 and B stable, Y must remain stable (A changes cannot affect Y).
    check_irrelevant_input_no_effect_s1: assert property (
        @(posedge clk) (S === 1'b1 && $past(S) === 1'b1 && $stable(B)) |-> $stable(Y)
    );
endmodule