module alu_slice_LA_sva (
    input  logic CLK,
    input  logic a,
    input  logic b,
    input  logic c,
    input  logic less,
    input  logic [2:0] sel,
    input  logic out,
    input  logic p,
    input  logic g
);
    // Helpers for past-valid and computed b^sel[2]
    logic past_valid;
    initial past_valid = 1'b0;
    always @(posedge CLK) past_valid <= 1'b1;

    logic b_xor;
    assign b_xor = sel[2] ^ b;

    ///// Functional checks /////
    // AND mode: out equals a & b when sel[1:0]==00.
    check_and_mode_out: assert property (
        @(posedge CLK) (sel[1:0] == 2'b00) |-> (out == (a & b))
    );

    // OR mode: out equals a | b when sel[1:0]==01.
    check_or_mode_out: assert property (
        @(posedge CLK) (sel[1:0] == 2'b01) |-> (out == (a | b))
    );

    // SUM mode: out equals a ^ (sel[2]^b) ^ c when sel[1:0]==10.
    check_sum_mode_out: assert property (
        @(posedge CLK) (sel[1:0] == 2'b10) |-> (out == (a ^ b_xor ^ c))
    );

    // SUM mode: p equals (a & (sel[2]^b)) | (a & c) | ((sel[2]^b) & c) when sel[1:0]==10.
    check_sum_mode_p: assert property (
        @(posedge CLK) (sel[1:0] == 2'b10) |-> (p == ((a & b_xor) | (a & c) | (b_xor & c)))
    );

    // SUM mode: g equals (a & (sel[2]^b)) | ((sel[2]^b) & c) when sel[1:0]==10.
    check_sum_mode_g: assert property (
        @(posedge CLK) (sel[1:0] == 2'b10) |-> (g == ((a & b_xor) | (b_xor & c)))
    );

    // COMPARE mode: out is 1 iff a<b (for 1-bit a,b) when sel[1:0]==11.
    check_compare_mode_out: assert property (
        @(posedge CLK) (sel[1:0] == 2'b11) |-> (out == ((!a) & b))
    );

    // COMPARE mode: less reflects a<b when sel[1:0]==11.
    check_compare_mode_less_value: assert property (
        @(posedge CLK) (sel[1:0] == 2'b11) |-> (less == ((!a) & b))
    );

    // COMPARE mode: less matches out when sel[1:0]==11.
    check_compare_mode_less_matches_out: assert property (
        @(posedge CLK) (sel[1:0] == 2'b11) |-> (less == out)
    );

    // less holds its value when not in COMPARE mode (sel[1:0]!=11).
    check_less_stable_when_not_compare: assert property (
        @(posedge CLK) past_valid && (sel[1:0] != 2'b11) |-> (less == $past(less))
    );

    // p holds its value when not in SUM mode (sel[1:0]!=10).
    check_p_stable_when_not_sum: assert property (
        @(posedge CLK) past_valid && (sel[1:0] != 2'b10) |-> (p == $past(p))
    );

    // g holds its value when not in SUM mode (sel[1:0]!=10).
    check_g_stable_when_not_sum: assert property (
        @(posedge CLK) past_valid && (sel[1:0] != 2'b10) |-> (g == $past(g))
    );

endmodule