module nor3_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C_N,
    input logic Y_wire,
    input logic A_wire,
    input logic B_wire,
    input logic C_N_wire
);

    // Top output mirrors the internal Y wire.
    check_output_matches_internal: assert property (
        @(posedge clk) Y === Y_wire
    );

    // Internal gate output implements the coded 3-input NOR.
    check_internal_nor_equation: assert property (
        @(posedge clk) Y_wire === ~(A_wire | B_wire | C_N_wire)
    );

    // Top output matches the NOR of the internal gate inputs.
    check_output_nor_equation: assert property (
        @(posedge clk) Y === ~(A_wire | B_wire | C_N_wire)
    );

    // All internal inputs low drives the internal output high.
    check_internal_high_when_all_inputs_low: assert property (
        @(posedge clk)
        ((A_wire === 1'b0) && (B_wire === 1'b0) && (C_N_wire === 1'b0))
        |-> (Y_wire === 1'b1)
    );

    // Internal A high forces the internal output low.
    check_internal_low_when_a_high: assert property (
        @(posedge clk) (A_wire === 1'b1) |-> (Y_wire === 1'b0)
    );

    // Internal B high forces the internal output low.
    check_internal_low_when_b_high: assert property (
        @(posedge clk) (B_wire === 1'b1) |-> (Y_wire === 1'b0)
    );

    // Internal C_N high forces the internal output low.
    check_internal_low_when_c_n_high: assert property (
        @(posedge clk) (C_N_wire === 1'b1) |-> (Y_wire === 1'b0)
    );

    // Internal output high implies all internal inputs are low.
    check_inputs_low_when_internal_output_high: assert property (
        @(posedge clk) (Y_wire === 1'b1)
        |-> ((A_wire === 1'b0) && (B_wire === 1'b0) && (C_N_wire === 1'b0))
    );

    // Internal output low implies at least one internal input is high.
    check_some_input_high_when_internal_output_low: assert property (
        @(posedge clk) (Y_wire === 1'b0)
        |-> ((A_wire === 1'b1) || (B_wire === 1'b1) || (C_N_wire === 1'b1))
    );

    // All internal inputs low drives the top output high.
    check_output_high_when_all_inputs_low: assert property (
        @(posedge clk)
        ((A_wire === 1'b0) && (B_wire === 1'b0) && (C_N_wire === 1'b0))
        |-> (Y === 1'b1)
    );

    // Any internal input high forces the top output low.
    check_output_low_when_any_input_high: assert property (
        @(posedge clk)
        ((A_wire === 1'b1) || (B_wire === 1'b1) || (C_N_wire === 1'b1))
        |-> (Y === 1'b0)
    );

endmodule