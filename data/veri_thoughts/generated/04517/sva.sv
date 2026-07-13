module comparator_sva (
    input logic       clk,
    input logic [3:0] V,
    input logic       z
);

    // z must match the RTL compare equation.
    check_output_equation: assert property (
        @(posedge clk) z == (V[3] & (V[2] | V[1]))
    );

    // z can only be high when V[3] is high.
    check_z_requires_v3: assert property (
        @(posedge clk) z |-> V[3]
    );

    // z can only be high when either V[2] or V[1] is high.
    check_z_requires_v2_or_v1: assert property (
        @(posedge clk) z |-> (V[2] | V[1])
    );

    // If V[3] is low, z must be low.
    check_v3_low_forces_z_low: assert property (
        @(posedge clk) !V[3] |-> !z
    );

    // If both V[2] and V[1] are low, z must be low.
    check_v2_v1_low_forces_z_low: assert property (
        @(posedge clk) !(V[2] | V[1]) |-> !z
    );

    // If V[3] and V[2] are high, z must be high.
    check_v3_and_v2_drive_z_high: assert property (
        @(posedge clk) (V[3] & V[2]) |-> z
    );

    // If V[3] and V[1] are high, z must be high.
    check_v3_and_v1_drive_z_high: assert property (
        @(posedge clk) (V[3] & V[1]) |-> z
    );

endmodule