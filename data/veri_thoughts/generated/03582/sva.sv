module sky130_fd_sc_ms__o22ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // Y matches the implemented O22AI combinational function.
    check_o22ai_function: assert property (
        @(posedge clk) Y === (~((A1 | A2) & (B1 | B2)))
    );

    // If one A input and one B input are high, Y must be low.
    check_low_when_both_input_groups_active: assert property (
        @(posedge clk) ((A1 | A2) & (B1 | B2)) |-> (Y === 1'b0)
    );

    // If both A inputs are low, Y must be high.
    check_high_when_a_group_inactive: assert property (
        @(posedge clk) ((~A1) & (~A2)) |-> (Y === 1'b1)
    );

    // If both B inputs are low, Y must be high.
    check_high_when_b_group_inactive: assert property (
        @(posedge clk) ((~B1) & (~B2)) |-> (Y === 1'b1)
    );

    // A low Y requires at least one A input to be high.
    check_low_output_requires_a_group_active: assert property (
        @(posedge clk) (Y === 1'b0) |-> (A1 | A2)
    );

    // A low Y requires at least one B input to be high.
    check_low_output_requires_b_group_active: assert property (
        @(posedge clk) (Y === 1'b0) |-> (B1 | B2)
    );

    // A high Y means at least one input group is entirely low.
    check_high_output_has_inactive_group: assert property (
        @(posedge clk) (Y === 1'b1) |-> (((~A1) & (~A2)) | ((~B1) & (~B2)))
    );

endmodule