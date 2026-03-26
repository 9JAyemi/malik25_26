module f3m_mux6_8bit_sva (
    input logic        clk,
    input logic [7:0]  v0,
    input logic [7:0]  v1,
    input logic [7:0]  v2,
    input logic [7:0]  v3,
    input logic [7:0]  v4,
    input logic [7:0]  v5,
    input logic        l0,
    input logic        l1,
    input logic        l2,
    input logic        l3,
    input logic        l4,
    input logic        l5,
    input logic        l6,
    input logic [7:0]  out
);

    // Output matches the RTL OR-of-selected-inputs equation.
    check_output_equation: assert property (
        @(posedge clk)
        out == ((v0 & {8{l0}}) |
                (v1 & {8{l1}}) |
                (v2 & {8{l2}}) |
                (v3 & {8{l3}}) |
                (v4 & {8{l4}}) |
                (v5 & {8{l5}}) |
                {8{(v0[7] & l6)}})
    );

    // With no select lines asserted, the output is zero.
    check_no_selects_zero: assert property (
        @(posedge clk)
        (!l0 && !l1 && !l2 && !l3 && !l4 && !l5 && !l6) |-> (out == 8'h00)
    );

    // With only l0 asserted, the output equals v0.
    check_only_l0_selected: assert property (
        @(posedge clk)
        ( l0 && !l1 && !l2 && !l3 && !l4 && !l5 && !l6) |-> (out == v0)
    );

    // With only l1 asserted, the output equals v1.
    check_only_l1_selected: assert property (
        @(posedge clk)
        (!l0 &&  l1 && !l2 && !l3 && !l4 && !l5 && !l6) |-> (out == v1)
    );

    // With only l2 asserted, the output equals v2.
    check_only_l2_selected: assert property (
        @(posedge clk)
        (!l0 && !l1 &&  l2 && !l3 && !l4 && !l5 && !l6) |-> (out == v2)
    );

    // With only l3 asserted, the output equals v3.
    check_only_l3_selected: assert property (
        @(posedge clk)
        (!l0 && !l1 && !l2 &&  l3 && !l4 && !l5 && !l6) |-> (out == v3)
    );

    // With only l4 asserted, the output equals v4.
    check_only_l4_selected: assert property (
        @(posedge clk)
        (!l0 && !l1 && !l2 && !l3 &&  l4 && !l5 && !l6) |-> (out == v4)
    );

    // With only l5 asserted, the output equals v5.
    check_only_l5_selected: assert property (
        @(posedge clk)
        (!l0 && !l1 && !l2 && !l3 && !l4 &&  l5 && !l6) |-> (out == v5)
    );

    // With only l6 asserted, v0[7] is broadcast to all output bits.
    check_only_l6_selected: assert property (
        @(posedge clk)
        (!l0 && !l1 && !l2 && !l3 && !l4 && !l5 &&  l6) |-> (out == {8{v0[7]}})
    );

endmodule