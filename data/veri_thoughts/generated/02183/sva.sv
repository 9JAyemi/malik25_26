module chatgpt_generate_JC_counter_sva (
    input logic        clk,
    input logic        rst_n,
    input logic [63:0] Q
);
    // Clock: clk; Reset: rst_n active-low async; Logic: sequential reg with comb next-state captured on clk.
    // Behavior: On reset Q=64'h1; when rst_n=1, Q[0]=~$past(Q[63]), Q[62:1]=$past(Q[61:0]) ^ {62{$past(Q[63])}}, Q[63]=$past(Q[62]}.

    ///// Reset behavior /////
    // While reset is asserted, Q is forced to 64'h1.
    check_reset_value: assert property (
        @(posedge clk) !rst_n |-> (Q == 64'h0000_0000_0000_0001)
    );

    // If reset stays asserted across cycles, Q remains 64'h1.
    check_reset_hold_value: assert property (
        @(posedge clk) (!rst_n && $past(!rst_n)) |-> (Q == 64'h0000_0000_0000_0001)
    );

    ///// Next-state mapping /////
    // Next Q[0] is the inverse of previous Q[63].
    check_next_bit0: assert property (
        @(posedge clk) disable iff (!rst_n) Q[0] == ~$past(Q[63])
    );

    // Next Q[62:1] equals previous Q[61:0] XORed with replicated previous Q[63].
    check_next_bits_62_to_1: assert property (
        @(posedge clk) disable iff (!rst_n) Q[62:1] == ($past(Q[61:0]) ^ {62{$past(Q[63])}})
    );

    // Next Q[63] equals previous Q[62].
    check_next_bit63: assert property (
        @(posedge clk) disable iff (!rst_n) Q[63] == $past(Q[62])
    );

    // When previous MSB was 0, Q[62:1] shifts without inversion.
    check_shift_no_invert_when_msb0: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(Q[63]) == 1'b0) |-> (Q[62:1] == $past(Q[61:0]))
    );

    // When previous MSB was 1, Q[62:1] is bitwise inverted shift.
    check_shift_invert_when_msb1: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(Q[63]) == 1'b1) |-> (Q[62:1] == ~$past(Q[61:0]))
    );

    // When previous MSB was 0, next Q[0] is 1.
    check_bit0_when_msb0: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(Q[63]) == 1'b0) |-> (Q[0] == 1'b1)
    );

    // When previous MSB was 1, next Q[0] is 0.
    check_bit0_when_msb1: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(Q[63]) == 1'b1) |-> (Q[0] == 1'b0)
    );

endmodule