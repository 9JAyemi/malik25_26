module top_module_assertions(
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic sel_b1,
    input logic sel_b2,
    input logic [3:0] out_always,
    input logic [3:0] out_and,
    input logic [3:0] out_or,
    input logic [3:0] out_xor
);

    // out_and equals a & b when both selects are high, else zero.
    check_out_and_gating: assert property (
        @(posedge clk)
        out_and == ((sel_b1 && sel_b2) ? (a & b) : 4'b0000)
    );

    // out_or equals a | b when both selects are high, else zero.
    check_out_or_gating: assert property (
        @(posedge clk)
        out_or == ((sel_b1 && sel_b2) ? (a | b) : 4'b0000)
    );

    // out_xor equals a ^ b when both selects are high, else zero.
    check_out_xor_gating: assert property (
        @(posedge clk)
        out_xor == ((sel_b1 && sel_b2) ? (a ^ b) : 4'b0000)
    );

    // With both selects low, out_always is the adder result a + a.
    check_out_always_sel00_add: assert property (
        @(posedge clk)
        ((sel_b1 == 1'b0) && (sel_b2 == 1'b0)) |-> (out_always == (a + a))
    );

    // With sel_b1 low and sel_b2 high, out_always forwards a.
    check_out_always_sel01_a: assert property (
        @(posedge clk)
        ((sel_b1 == 1'b0) && (sel_b2 == 1'b1)) |-> (out_always == a)
    );

    // With sel_b1 high and sel_b2 low, out_always forwards a.
    check_out_always_sel10_a: assert property (
        @(posedge clk)
        ((sel_b1 == 1'b1) && (sel_b2 == 1'b0)) |-> (out_always == a)
    );

    // With both selects high, out_always forwards b.
    check_out_always_sel11_b: assert property (
        @(posedge clk)
        ((sel_b1 == 1'b1) && (sel_b2 == 1'b1)) |-> (out_always == b)
    );

endmodule