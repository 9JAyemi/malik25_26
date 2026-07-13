module OAI21B2HD4X_assertions (
    input logic clk,
    input logic AN,
    input logic BN,
    input logic C,
    input logic Z
);

    // Z matches the implemented combinational function.
    check_boolean_function: assert property (
        @(posedge clk) Z == ((~(AN & BN)) & C)
    );

    // C low forces Z low.
    check_c_low_forces_z_low: assert property (
        @(posedge clk) !C |-> !Z
    );

    // AN and BN both high block the output when C is high.
    check_an_bn_high_block_output: assert property (
        @(posedge clk) (C && AN && BN) |-> !Z
    );

    // AN low with C high makes Z high.
    check_an_low_allows_output: assert property (
        @(posedge clk) (C && !AN) |-> Z
    );

    // BN low with C high makes Z high.
    check_bn_low_allows_output: assert property (
        @(posedge clk) (C && !BN) |-> Z
    );

    // A high Z requires C to be high.
    check_z_high_requires_c_high: assert property (
        @(posedge clk) Z |-> C
    );

    // A high Z requires the AN/BN AND term to be false.
    check_z_high_requires_inverted_and: assert property (
        @(posedge clk) Z |-> !(AN && BN)
    );

endmodule