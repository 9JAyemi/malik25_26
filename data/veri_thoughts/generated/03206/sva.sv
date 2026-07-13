module my_module_assertions (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic Y,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // No explicit clock or reset exists in the RTL; sample on the global clock.
    // Y must match the implemented combinational equation.
    check_output_equation: assert property (
        @($global_clock) disable iff (1'b0)
        Y == ((A1 && !A2) || (!A1 && A2) || B1)
    );

    // B1 being high must force Y high.
    check_b1_forces_y_high: assert property (
        @($global_clock) disable iff (1'b0)
        B1 |-> Y
    );

    // With B1 low, Y must reduce to the XOR of A1 and A2.
    check_xor_when_b1_low: assert property (
        @($global_clock) disable iff (1'b0)
        !B1 |-> (Y == ((A1 && !A2) || (!A1 && A2)))
    );

    // With B1 low and equal A inputs, Y must be low.
    check_equal_inputs_clear_y: assert property (
        @($global_clock) disable iff (1'b0)
        (!B1 && ((A1 && A2) || (!A1 && !A2))) |-> !Y
    );

    // With B1 low and different A inputs, Y must be high.
    check_different_inputs_set_y: assert property (
        @($global_clock) disable iff (1'b0)
        (!B1 && ((A1 && !A2) || (!A1 && A2))) |-> Y
    );

endmodule