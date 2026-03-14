module top_module_sva (
    input logic clk,                 // Property clock (RTL has no clock)
    input logic [3:0] in_vec,
    input logic [3:0] out_vec,
    input logic msb_out,
    input logic mid_out,
    input logic lsb_out
);
    // RTL is pure combinational; no reset; assertions are clocked on clk.

    // out_vec[0] equals in_vec[0].
    check_out0_eq_in0: assert property (
        @(posedge clk) out_vec[0] == in_vec[0]
    );

    // out_vec[1] equals in_vec[1] ^ in_vec[0].
    check_out1_eq_in1_xor_in0: assert property (
        @(posedge clk) out_vec[1] == (in_vec[1] ^ in_vec[0])
    );

    // out_vec[2] equals in_vec[2] ^ in_vec[1] ^ in_vec[0].
    check_out2_eq_in2_xor_in1_xor_in0: assert property (
        @(posedge clk) out_vec[2] == (in_vec[2] ^ in_vec[1] ^ in_vec[0])
    );

    // out_vec[3] equals in_vec[3] ^ in_vec[2] ^ in_vec[1] ^ in_vec[0].
    check_out3_eq_in3_xor_in2_xor_in1_xor_in0: assert property (
        @(posedge clk) out_vec[3] == (in_vec[3] ^ in_vec[2] ^ in_vec[1] ^ in_vec[0])
    );

    // msb_out passes through in_vec[3].
    check_msb_passthrough: assert property (
        @(posedge clk) msb_out == in_vec[3]
    );

    // mid_out passes through in_vec[1].
    check_mid_passthrough: assert property (
        @(posedge clk) mid_out == in_vec[1]
    );

    // lsb_out passes through in_vec[0].
    check_lsb_passthrough: assert property (
        @(posedge clk) lsb_out == in_vec[0]
    );

    // Recursive relation: out_vec[1] equals in_vec[1] ^ out_vec[0].
    check_out1_rel_out0: assert property (
        @(posedge clk) out_vec[1] == (in_vec[1] ^ out_vec[0])
    );

    // Recursive relation: out_vec[2] equals in_vec[2] ^ out_vec[1].
    check_out2_rel_out1: assert property (
        @(posedge clk) out_vec[2] == (in_vec[2] ^ out_vec[1])
    );

    // Recursive relation: out_vec[3] equals in_vec[3] ^ out_vec[2].
    check_out3_rel_out2: assert property (
        @(posedge clk) out_vec[3] == (in_vec[3] ^ out_vec[2])
    );

    // If in_vec is stable, all outputs remain stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) $stable(in_vec) |-> $stable(out_vec) && $stable(msb_out) && $stable(mid_out) && $stable(lsb_out)
    );

endmodule