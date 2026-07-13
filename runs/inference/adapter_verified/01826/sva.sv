module hls_contrast_streibs_sva (
    input logic clk,
    input logic [0:0] din0,
    input logic [0:0] din1,
    input logic [0:0] din2,
    input logic [0:0] dout
);

// No reset in RTL; sample combinational behavior on clk.

    // dout equals din0 * din1 + din2.
    check_functional_equivalence: assert property (
        @(posedge clk) dout == (din0 * din1) + din2
    );

// When din2 is zero, dout equals din0 * din1.
    check_din2_zero_passthrough: assert property (
        @(posedge clk) (din2 == 1'b0) |-> (dout == (din0 * din1))
    );

// When din1 is zero, dout equals din2.
    check_din1_zero_passthrough: assert property (
        @(posedge clk) (din1 == 1'b0) |-> (dout == din2)
    );

// When din0 is zero, dout equals din2.
    check_din0_zero_passthrough: assert property (
        @(posedge clk) (din0 == 1'b0) |-> (dout == din2)
    );

// When din1 is one, dout equals din0 + din2.
    check_din1_one_passthrough: assert property (
        @(posedge clk) (din1 == 1'b1) |-> (dout == (din0 + din2))
    );

// When din0 is one, dout equals din1 + din2.
    check_din0_one_passthrough: assert property (
        @(posedge clk) (din0 == 1'b1) |-> (dout == (din1 + din2))
    );

// When din1 is one and din2 is zero, dout equals din0.
    check_din1_one_din2_zero_passthrough: assert property (
        @(posedge clk) ((din1 == 1'b1) && (din2 == 1'b0)) |-> (dout == din0)
    );

// When din0 is one and din2 is zero, dout equals din1.
    check_din0_one_din2_zero_passthrough: assert property (
        @(posedge clk) ((din0 == 1'b1) && (din2 == 1'b0)) |-> (dout == din1)
    );

// When din0 equals din1, dout equals 2 * din0 + din2.
    check_equal_inputs_double: assert property (
        @(posedge clk) (din0 == din1) |-> (dout == ((din0 + din0) + din2))
    );

endmodule
