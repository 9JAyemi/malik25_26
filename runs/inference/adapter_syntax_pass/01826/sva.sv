module hls_contrast_streibs_sva #(
    parameter int din0_WIDTH = 1,
    parameter int din1_WIDTH = 1,
    parameter int din2_WIDTH = 1,
    parameter int dout_WIDTH = 1
) (
    input logic clk,
    input logic [din0_WIDTH-1:0] din0,
    input logic [din1_WIDTH-1:0] din1,
    input logic [din2_WIDTH-1:0] din2,
    input logic [dout_WIDTH-1:0] dout
);

    // dout must equal the 1-bit product of din0 and din1 plus din2.
    check_dout_matches_product_plus_din2: assert property (
        @(posedge clk)
        dout == ((din0 & din1) | din2)
    );

    // A zero din2 must pass through the product term.
    check_zero_din2_passes_product: assert property (
        @(posedge clk)
        (din2 == {din2_WIDTH{1'b0}}) |-> (dout == (din0 & din1))
    );

    // A zero din0 must force the output low.
    check_zero_din0_forces_low: assert property (
        @(posedge clk)
        (din0 == {din0_WIDTH{1'b0}}) |-> (dout == {dout_WIDTH{1'b0}})
    );

    // A zero din1 must force the output low.
    check_zero_din1_forces_low: assert property (
        @(posedge clk)
        (din1 == {din1_WIDTH{1'b0}}) |-> (dout == {dout_WIDTH{1'b0}})
    );

    // A high din2 must force the output high.
    check_high_din2_forces_high: assert property (
        @(posedge clk)
        (din2[din2_WIDTH-1]) |-> (dout[dout_WIDTH-1])
    );

    // A high product term must force the output high.
    check_high_product_forces_high: assert property (
        @(posedge clk)
        (din0[din0_WIDTH-1] & din1[din1_WIDTH-1]) |-> (dout[dout_WIDTH-1])
    );

    // A low product term must force the output low when din2 is low.
    check_low_product_with_zero_din2_forces_low: assert property (
        @(posedge clk)
        ((!din0[din0_WIDTH-1] || !din1[din1_WIDTH-1]) && (din2 == {din2_WIDTH{1'b0}})) |-> (dout == {dout_WIDTH{1'b0}})
    );

endmodule