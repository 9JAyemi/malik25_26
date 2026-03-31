module hls_contrast_streibs_sva (
    input logic CLK,
    input logic [0:0] din0,
    input logic [0:0] din1,
    input logic [0:0] din2,
    input logic [0:0] dout
);
    // Combinational DUT with no reset; sample on CLK.

    // dout equals (din0 * din1) + din2.
    check_functional_relation: assert property (
        @(posedge CLK) dout == ((din0 * din1) + din2)
    );

    // If din0 is 0, dout equals din2.
    check_zero_din0: assert property (
        @(posedge CLK) (din0 == 1'b0) |-> (dout == din2)
    );

    // If din1 is 0, dout equals din2.
    check_zero_din1: assert property (
        @(posedge CLK) (din1 == 1'b0) |-> (dout == din2)
    );

    // If din2 is 0, dout equals din0 * din1.
    check_zero_din2: assert property (
        @(posedge CLK) (din2 == 1'b0) |-> (dout == (din0 * din1))
    );

    // If din0 and din1 are 1, dout equals 1 (mod 2).
    check_one_inputs: assert property (
        @(posedge CLK) ((din0 == 1'b1) && (din1 == 1'b1)) |-> (dout == 1'b1)
    );

    // If din0 and din1 are 0, dout equals 0.
    check_zero_inputs: assert property (
        @(posedge CLK) ((din0 == 1'b0) && (din1 == 1'b0)) |-> (dout == 1'b0)
    );

    // If din2 equals din0 * din1, dout equals din2.
    check_din2_equals_mul: assert property (
        @(posedge CLK) (din2 == (din0 * din1)) |-> (dout == din2)
    );

    // If din0 equals din1, dout equals din0 + din2.
    check_din0_eq_din1: assert property (
        @(posedge CLK) (din0 == din1) |-> (dout == (din0 + din2))
    );

    // If din0 equals 1, dout equals din1 + din2.
    check_din0_one: assert property (
        @(posedge CLK) (din0 == 1'b1) |-> (dout == (din1 + din2))
    );

    // If din1 equals 1, dout equals din0 + din2.
    check_din1_one: assert property (
        @(posedge CLK) (din1 == 1'b1) |-> (dout == (din0 + din2))
    );

    // If din0 equals 0, dout equals din2.
    check_din0_zero: assert property (
        @(posedge CLK) (din0 == 1'b0) |-> (dout == din2)
    );

    // If din1 equals 0, dout equals din2.
    check_din1_zero: assert property (
        @(posedge CLK) (din1 == 1'b0) |-> (dout == din2)
    );

    // If din0 and din1 are stable, dout is stable (independent of din2).
    check_stability_independent_of_din2: assert property (
        @(posedge CLK) ($stable(din0) && $stable(din1)) |-> $stable(dout)
    );

    // If din0 and din1 are stable, dout equals (din0 * din1) + din2.
    check_functional_relation_stable: assert property (
        @(posedge CLK) ($stable(din0) && $stable(din1)) |-> (dout == ((din0 * din1) + din2))
    );

    // If din0, din1, and din2 are stable, dout is stable.
    check_stability_all_inputs: assert property (
        @(posedge CLK) ($stable(din0) && $stable(din1) && $stable(din2)) |-> $stable(dout)
    );
endmodule