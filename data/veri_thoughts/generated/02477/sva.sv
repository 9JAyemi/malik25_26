module mux_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic invert,
    input logic out
);
    // out equals (C ? B : A) XOR invert.
    check_mux_function: assert property (
        @(posedge clk) out == ((C ? B : A) ^ invert)
    );

    // When C==0, out equals A XOR invert.
    check_C0_path: assert property (
        @(posedge clk) (C == 1'b0) |-> (out == (A ^ invert))
    );

    // When C==1, out equals B XOR invert.
    check_C1_path: assert property (
        @(posedge clk) (C == 1'b1) |-> (out == (B ^ invert))
    );

    // When invert==0, out equals selected input.
    check_invert0_behavior: assert property (
        @(posedge clk) (invert == 1'b0) |-> (out == (C ? B : A))
    );

    // When invert==1, out equals inverse of selected input.
    check_invert1_behavior: assert property (
        @(posedge clk) (invert == 1'b1) |-> (out == ~(C ? B : A))
    );

    // If inputs are stable, out remains stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(C) && $stable(invert)) |-> $stable(out)
    );

    // If only invert changes (others stable), out toggles.
    check_out_toggles_on_invert_change: assert property (
        @(posedge clk) $past(1'b1) && $stable(A) && $stable(B) && $stable(C) && $changed(invert) |-> (out == ~$past(out))
    );

    // With C==0 and others stable, A change causes out to change to A^invert.
    check_A_influence_when_C0: assert property (
        @(posedge clk) $past(1'b1) && (C == 1'b0) && $stable(B) && $stable(C) && $stable(invert) && $changed(A) |-> ($changed(out) && (out == (A ^ invert)))
    );

    // With C==1 and others stable, B change causes out to change to B^invert.
    check_B_influence_when_C1: assert property (
        @(posedge clk) $past(1'b1) && (C == 1'b1) && $stable(A) && $stable(C) && $stable(invert) && $changed(B) |-> ($changed(out) && (out == (B ^ invert)))
    );

    // With C==1 and others stable, A change does not affect out.
    check_A_no_influence_when_C1: assert property (
        @(posedge clk) $past(1'b1) && (C == 1'b1) && $stable(B) && $stable(C) && $stable(invert) && $changed(A) |-> !$changed(out)
    );

    // With C==0 and others stable, B change does not affect out.
    check_B_no_influence_when_C0: assert property (
        @(posedge clk) $past(1'b1) && (C == 1'b0) && $stable(A) && $stable(C) && $stable(invert) && $changed(B) |-> !$changed(out)
    );
endmodule