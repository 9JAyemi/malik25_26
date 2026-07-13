module chacha_qr_sva (
    input wire [31 : 0] a,
    input wire [31 : 0] b,
    input wire [31 : 0] c,
    input wire [31 : 0] d,

    output wire [31 : 0] a_prim,
    output wire [31 : 0] b_prim,
    output wire [31 : 0] c_prim,
    output wire [31 : 0] d_prim
);

    // Combinational logic, so use @(posedge clk)
    // No clock or reset signals are present in the RTL

    // Check that the outputs are correctly assigned from internal registers
    output_assignment_a: assert property (
        @(posedge clk) disable iff (!RESETn) (a_prim == internal_a_prim)
    ) else $error("a_prim is not correctly assigned from internal_a_prim");

    output_assignment_b: assert property (
        @(posedge clk) disable iff (!RESETn) (b_prim == internal_b_prim)
    ) else $error("b_prim is not correctly assigned from internal_b_prim");

    output_assignment_c: assert property (
        @(posedge clk) disable iff (!RESETn) (c_prim == internal_c_prim)
    ) else $error("c_prim is not correctly assigned from internal_c_prim");

    output_assignment_d: assert property (
        @(posedge clk) disable iff (!RESETn) (d_prim == internal_d_prim)
    ) else $error("d_prim is not correctly assigned from internal_d_prim");

    // Check that the internal registers are correctly updated
    internal_update_a: assert property (
        @(posedge clk) disable iff (!RESETn) (internal_a_prim == a1)
    ) else $error("internal_a_prim is not correctly updated");

    internal_update_b: assert property (
        @(posedge clk) disable iff (!RESETn) (internal_b_prim == b3)
    ) else $error("internal_b_prim is not correctly updated");

    internal_update_c: assert property (
        @(posedge clk) disable iff (!RESETn) (internal_c_prim == c1)
    ) else $error("internal_c_prim is not correctly updated");

    internal_update_d: assert property (
        @(posedge clk) disable iff (!RESETn) (internal_d_prim == d3)
    ) else $error("internal_d_prim is not correctly updated");

    // Check that the intermediate calculations are correct
    intermediate_calc_a0: assert property (
        @(posedge clk) disable iff (!RESETn) (a0 == a + b)
    ) else $error("a0 is not correctly calculated");

    intermediate_calc_d0: assert property (
        @(posedge clk) disable iff (!RESETn) (d0 == d ^ a0)
    ) else $error("d0 is not correctly calculated");

    intermediate_calc_d1: assert property (
        @(posedge clk) disable iff (!RESETn) (d1 == {d0[15 : 0], d0[31 : 16]})
    ) else $error("d1 is not correctly calculated");

    intermediate_calc_c0: assert property (
        @(posedge clk) disable iff (!RESETn) (c0 == c + d1)
    ) else $error("c0 is not correctly calculated");

    intermediate_calc_b0: assert property (
        @(posedge clk) disable iff (!RESETn) (b0 == b ^ c0)
    ) else $error("b0 is not correctly calculated");

    intermediate_calc_b1: assert property (
        @(posedge clk) disable iff (!RESETn) (b1 == {b0[19 : 0], b0[31 : 20]})
    ) else $error("b1 is not correctly calculated");

    intermediate_calc_a1: assert property (
        @(posedge clk) disable iff (!RESETn) (a1 == a0 + b1)
    ) else $error("a1 is not correctly calculated");

    intermediate_calc_d2: assert property (
        @(posedge clk) disable iff (!RESETn) (d2 == d1 ^ a1)
    ) else $error("d2 is not correctly calculated");

    intermediate_calc_d3: assert property (
        @(posedge clk) disable iff (!RESETn) (d3 == {d2[23 : 0], d2[31 : 24]})
    ) else $error("d3 is not correctly calculated");

    intermediate_calc_c1: assert property (
        @(posedge clk) disable iff (!RESETn) (c1 == c0 + d3)
    ) else $error("c1 is not correctly calculated");

    intermediate_calc_b2: assert property (
        @(posedge clk) disable iff (!RESETn) (b2 == b1 ^ c1)
    ) else $error("b2 is not correctly calculated");

    intermediate_calc_b3: assert property (
        @(posedge clk) disable iff (!RESETn) (b3 == {b2[24 : 0], b2[31 : 25]})
    ) else $error("b3 is not correctly calculated");

endmodule