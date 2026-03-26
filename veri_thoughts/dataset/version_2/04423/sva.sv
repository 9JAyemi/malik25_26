module mux_2to1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic SEL,
    input logic OUT
);

    // When SEL changes to 0, OUT updates to A.
    check_sel_change_selects_a: assert property (
        @(posedge clk)
        !$initstate && (SEL !== $past(SEL)) && (SEL === 1'b0) |-> (OUT === A)
    );

    // When SEL changes away from 0, OUT updates to B.
    check_sel_change_selects_b: assert property (
        @(posedge clk)
        !$initstate && (SEL !== $past(SEL)) && (SEL !== 1'b0) |-> (OUT === B)
    );

    // Without a SEL change, OUT holds its previous value.
    check_out_holds_without_sel_change: assert property (
        @(posedge clk)
        !$initstate && (SEL === $past(SEL)) |-> (OUT === $past(OUT))
    );

    // A changes alone do not update OUT.
    check_a_change_ignored_without_sel_change: assert property (
        @(posedge clk)
        !$initstate && (A !== $past(A)) && (SEL === $past(SEL)) |-> (OUT === $past(OUT))
    );

    // B changes alone do not update OUT.
    check_b_change_ignored_without_sel_change: assert property (
        @(posedge clk)
        !$initstate && (B !== $past(B)) && (SEL === $past(SEL)) |-> (OUT === $past(OUT))
    );

endmodule