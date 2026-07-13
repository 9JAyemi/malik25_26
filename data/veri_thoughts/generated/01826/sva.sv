module hls_contrast_streibs_sva #(
    parameter ID = 32'd1,
    parameter NUM_STAGE = 32'd1,
    parameter din0_WIDTH = 32'd1,
    parameter din1_WIDTH = 32'd1,
    parameter din2_WIDTH = 32'd1,
    parameter dout_WIDTH = 32'd1
) (
    input  logic                     CLK,
    input  logic [din0_WIDTH - 1:0]  din0,
    input  logic [din1_WIDTH - 1:0]  din1,
    input  logic [din2_WIDTH - 1:0]  din2,
    input  logic [dout_WIDTH - 1:0]  dout
);
    // Mask of dout width (used to model truncation/modulo 2^W behavior)
    localparam logic [dout_WIDTH-1:0] DOUT_MASK = {dout_WIDTH{1'b1}};

    ///// Functional equivalence to RTL logic /////
    // dout equals ((din0*din1) truncated to W) + din2, truncated to W.
    check_dout_mac_modulo: assert property (
        @(posedge CLK) disable iff (1'b0)
            dout == ((((din0 * din1) & DOUT_MASK) + din2) & DOUT_MASK)
    );

    ///// Arithmetic corner cases /////
    // If din0 is zero, dout equals din2 truncated to W.
    check_zero_multiplicand_din0: assert property (
        @(posedge CLK) disable iff (1'b0)
            (din0 == '0) |-> (dout == (din2 & DOUT_MASK))
    );
    // If din1 is zero, dout equals din2 truncated to W.
    check_zero_multiplicand_din1: assert property (
        @(posedge CLK) disable iff (1'b0)
            (din1 == '0) |-> (dout == (din2 & DOUT_MASK))
    );
    // If din2 is zero, dout equals (din0*din1) truncated to W.
    check_zero_addend: assert property (
        @(posedge CLK) disable iff (1'b0)
            (din2 == '0) |-> (dout == ((din0 * din1) & DOUT_MASK))
    );
    // If din0 is one, dout equals (din1 + din2) truncated to W.
    check_mul_by_one_din0: assert property (
        @(posedge CLK) disable iff (1'b0)
            (din0 == {{(din0_WIDTH-1){1'b0}},1'b1}) |-> (dout == ((din1 + din2) & DOUT_MASK))
    );
    // If din1 is one, dout equals (din0 + din2) truncated to W.
    check_mul_by_one_din1: assert property (
        @(posedge CLK) disable iff (1'b0)
            (din1 == {{(din1_WIDTH-1){1'b0}},1'b1}) |-> (dout == ((din0 + din2) & DOUT_MASK))
    );

    ///// Combinational consistency /////
    // If inputs are stable, dout remains stable (pure combinational behavior).
    check_stable_out_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (1'b0)
            ($stable(din0) && $stable(din1) && $stable(din2)) |-> $stable(dout)
    );

endmodule