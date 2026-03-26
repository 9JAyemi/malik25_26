module mux_3to1_with_outputs_sva (
    input logic [2:0] in_vec,
    input logic sel,
    input logic [2:0] out_vec,
    input logic o2,
    input logic o1,
    input logic o0,
    input logic clk
);

    // No RTL clock or reset; clk is only for assertion sampling.

    // o0 directly reflects in_vec[0].
    check_o0_pass_through: assert property (
        @(posedge clk) o0 == in_vec[0]
    );

    // o1 directly reflects in_vec[1].
    check_o1_pass_through: assert property (
        @(posedge clk) o1 == in_vec[1]
    );

    // o2 directly reflects in_vec[2].
    check_o2_pass_through: assert property (
        @(posedge clk) o2 == in_vec[2]
    );

    // With sel low, out_vec matches in_vec.
    check_out_vec_sel_low: assert property (
        @(posedge clk) !sel |-> (out_vec == in_vec)
    );

    // With sel high, out_vec preserves bit 2 and ORs adjacent lower bits.
    check_out_vec_sel_high: assert property (
        @(posedge clk) sel |-> (out_vec == {in_vec[2], (in_vec[2] | in_vec[1]), (in_vec[1] | in_vec[0])})
    );

endmodule