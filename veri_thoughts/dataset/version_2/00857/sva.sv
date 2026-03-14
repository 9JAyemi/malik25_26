module mux_2_to_1_sva (
    input logic clk,   // external sampling clock for SVA
    input logic a,
    input logic b,
    input logic sel,
    input logic out,
    input logic w1
);
    // Clocks: none in RTL; Reset: none; Logic: pure combinational.
    // Key behavior: out = (sel ? b : a); w1 = (~sel & a). Assertions sampled on clk.

    // w1 equals ~sel & a.
    check_w1_definition: assert property (
        @(posedge clk) w1 == ((~sel) & a)
    );

    // out equals (sel & b) | w1.
    check_out_sum_of_terms: assert property (
        @(posedge clk) out == ((sel & b) | w1)
    );

    // When sel=1, out must equal b.
    check_sel1_routes_b: assert property (
        @(posedge clk) sel |-> (out == b)
    );

    // When sel=0, out must equal a.
    check_sel0_routes_a: assert property (
        @(posedge clk) (~sel) |-> (out == a)
    );

    // If sel=1 then w1 must be 0.
    check_w1_zero_when_sel1: assert property (
        @(posedge clk) sel |-> (w1 == 1'b0)
    );

    // If a=0 then w1 must be 0.
    check_w1_zero_when_a0: assert property (
        @(posedge clk) (~a) |-> (w1 == 1'b0)
    );

    // If sel=1 and b=1 then out must be 1.
    check_out1_when_sel1_b1: assert property (
        @(posedge clk) (sel & b) |-> (out == 1'b1)
    );

    // If sel=1 and b=0 then out must be 0.
    check_out0_when_sel1_b0: assert property (
        @(posedge clk) (sel & (~b)) |-> (out == 1'b0)
    );

    // If sel=0 and a=1 then out must be 1.
    check_out1_when_sel0_a1: assert property (
        @(posedge clk) ((~sel) & a) |-> (out == 1'b1)
    );

    // If sel=0 and a=0 then out must be 0.
    check_out0_when_sel0_a0: assert property (
        @(posedge clk) ((~sel) & (~a)) |-> (out == 1'b0)
    );
endmodule