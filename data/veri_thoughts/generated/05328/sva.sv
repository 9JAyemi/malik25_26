module conditional_output_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] C,
    input logic clk,
    input logic [3:0] out
);

    // C=2'b10 selects A^B, registered to out on the next cycle.
    check_c10_selects_xor_next_cycle: assert property (
        @(posedge clk)
        (C === 2'b10) |=> (out === ($past(A) ^ $past(B)))
    );

    // C=2'b01 selects B, registered to out on the next cycle.
    check_c01_selects_b_next_cycle: assert property (
        @(posedge clk)
        (C === 2'b01) |=> (out === $past(B))
    );

    // All other C values select A, registered to out on the next cycle.
    check_default_selects_a_next_cycle: assert property (
        @(posedge clk)
        ((C !== 2'b10) && (C !== 2'b01)) |=> (out === $past(A))
    );

    // out always matches the prior cycle's selected value.
    check_out_matches_delayed_selected_value: assert property (
        @(posedge clk)
        1'b1 |=> (
            (($past(C) === 2'b10) && (out === ($past(A) ^ $past(B)))) ||
            (($past(C) === 2'b01) && (out === $past(B))) ||
            (($past(C) !== 2'b10) && ($past(C) !== 2'b01) && (out === $past(A)))
        )
    );

    // out holds when the current selected value already equals out.
    check_out_holds_when_selected_value_repeats: assert property (
        @(posedge clk)
        (((C === 2'b10) && ((A ^ B) === out)) ||
         ((C === 2'b01) && (B === out)) ||
         ((C !== 2'b10) && (C !== 2'b01) && (A === out)))
        |=> (out === $past(out))
    );

    // out changes when the current selected value differs from out.
    check_out_changes_when_selected_value_differs: assert property (
        @(posedge clk)
        (((C === 2'b10) && ((A ^ B) !== out)) ||
         ((C === 2'b01) && (B !== out)) ||
         ((C !== 2'b10) && (C !== 2'b01) && (A !== out)))
        |=> (out !== $past(out))
    );

endmodule