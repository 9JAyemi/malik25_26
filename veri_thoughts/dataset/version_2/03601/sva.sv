module and_gate_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic VPWR,
    input logic VGND
);

    // X must match the implemented combinational function.
    check_exact_function: assert property (
        @(posedge clk) X == ((A1 & A2) & (VPWR > VGND))
    );

    // A low A1 input forces X low.
    check_a1_low_forces_x_low: assert property (
        @(posedge clk) !A1 |-> !X
    );

    // A low A2 input forces X low.
    check_a2_low_forces_x_low: assert property (
        @(posedge clk) !A2 |-> !X
    );

    // An invalid power comparison forces X low.
    check_power_not_good_forces_x_low: assert property (
        @(posedge clk) !(VPWR > VGND) |-> !X
    );

    // A high X requires both inputs high and power valid.
    check_x_high_requires_inputs_and_power: assert property (
        @(posedge clk) X |-> (A1 && A2 && (VPWR > VGND))
    );

    // Both inputs high with valid power must drive X high.
    check_all_conditions_drive_x_high: assert property (
        @(posedge clk) (A1 && A2 && (VPWR > VGND)) |-> X
    );

endmodule