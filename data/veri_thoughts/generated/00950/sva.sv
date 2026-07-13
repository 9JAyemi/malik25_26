module usb_type_c_orientation_sva (
    input logic CLK,
    input logic cc1,
    input logic cc2,
    input logic orientation
);
    // Orientation must be 1 when cc1=1 and cc2=0.
    check_orient_A_forward: assert property (
        @(posedge CLK) (cc1 === 1'b1) && (cc2 === 1'b0) |-> (orientation === 1'b1)
    );

    // Orientation must be 0 when cc1=0 and cc2=1.
    check_orient_B_forward: assert property (
        @(posedge CLK) (cc1 === 1'b0) && (cc2 === 1'b1) |-> (orientation === 1'b0)
    );

    // Orientation can be 1 only if cc1=1 and cc2=0.
    check_orient_A_reverse: assert property (
        @(posedge CLK) (orientation === 1'b1) |-> ((cc1 === 1'b1) && (cc2 === 1'b0))
    );

    // Orientation can be 0 only if cc1=0 and cc2=1.
    check_orient_B_reverse: assert property (
        @(posedge CLK) (orientation === 1'b0) |-> ((cc1 === 1'b0) && (cc2 === 1'b1))
    );

    // On cc1 rising edge with cc2 low, orientation must be 1 in the same cycle.
    check_orient_on_cc1_rise: assert property (
        @(posedge CLK) ($rose(cc1) && (cc2 === 1'b0)) |-> (orientation === 1'b1)
    );

    // On cc2 rising edge with cc1 low, orientation must be 0 in the same cycle.
    check_orient_on_cc2_rise: assert property (
        @(posedge CLK) ($rose(cc2) && (cc1 === 1'b0)) |-> (orientation === 1'b0)
    );
endmodule