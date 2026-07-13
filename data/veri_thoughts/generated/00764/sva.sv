module xor_inv_multiplexer_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic sel_b1,
    input logic sel_b2,
    input logic sel_out,
    input logic out_always,
    input logic [3:0] out_xor,
    input logic [3:0] out_xor_inv,
    input logic out_logical_inv
);
    // out_xor equals (sel_b2 ? b : (sel_b1 ? b : a)) XOR a.
    check_out_xor_from_mux: assert property (
        @(posedge clk) out_xor == ((sel_b2 ? b : (sel_b1 ? b : a)) ^ a)
    );

    // out_xor_inv is bitwise inverse of out_xor.
    check_out_xor_inv_is_not: assert property (
        @(posedge clk) out_xor_inv == ~out_xor
    );

    // out_logical_inv is logical NOT of out_xor (NOR-reduction).
    check_out_logical_inv_is_nor: assert property (
        @(posedge clk) out_logical_inv == ~(|out_xor)
    );

    // When sel_b2 is 1, b is selected and out_xor equals b ^ a.
    check_sel_b2_drives_b_xor_a: assert property (
        @(posedge clk) sel_b2 |-> (out_xor == (b ^ a))
    );

    // When sel_b2 is 0 and sel_b1 is 1, b is selected and out_xor equals b ^ a.
    check_sel_b1_drives_when_b2_low: assert property (
        @(posedge clk) (!sel_b2 && sel_b1) |-> (out_xor == (b ^ a))
    );

    // When both sel_b2 and sel_b1 are 0, a is selected and out_xor is zero (a ^ a).
    check_both_selects_zero_xor_zero: assert property (
        @(posedge clk) (!sel_b2 && !sel_b1) |-> (out_xor == 4'b0000)
    );

    // When both selects are 0, out_xor_inv is all ones (~0).
    check_both_selects_zero_inv_ones: assert property (
        @(posedge clk) (!sel_b2 && !sel_b1) |-> (out_xor_inv == 4'b1111)
    );

    // When out_xor is zero, out_logical_inv must be 1.
    check_xor_zero_implies_logical_inv_one: assert property (
        @(posedge clk) (out_xor == 4'b0000) |-> (out_logical_inv == 1'b1)
    );

    // On the next cycle after sel_out==0, out_always equals previous out_xor_inv.
    check_out_always_follows_prev_xor_inv_sel0: assert property (
        @(posedge clk) $past(1'b1) && ($past(sel_out) == 1'b0) |-> (out_always == $past(out_xor_inv))
    );

    // On the next cycle after sel_out==1, out_always equals previous out_logical_inv.
    check_out_always_follows_prev_logical_inv_sel1: assert property (
        @(posedge clk) $past(1'b1) && ($past(sel_out) == 1'b1) |-> (out_always == $past(out_logical_inv))
    );
endmodule