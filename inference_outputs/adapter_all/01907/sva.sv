module and_module_sva (
    input logic        clk,
    input logic [7:0]  i_bus1,
    input logic [7:0]  i_bus2,
    input logic [7:0]  o_bus
);

    // Output must equal the bitwise AND of the two inputs.
    check_and_function: assert property (
        @(posedge clk) o_bus == (i_bus1 & i_bus2)
    );

    // A zero on i_bus1 must force a zero on o_bus.
    check_zero_mask_i_bus1: assert property (
        @(posedge clk) (i_bus1 == 8'h00) |-> (o_bus == 8'h00)
    );

    // A zero on i_bus2 must force a zero on o_bus.
    check_zero_mask_i_bus2: assert property (
        @(posedge clk) (i_bus2 == 8'h00) |-> (o_bus == 8'h00)
    );

    // All ones on i_bus1 must pass i_bus2 through to o_bus.
    check_pass_through_i_bus1: assert property (
        @(posedge clk) (i_bus1 == 8'hFF) |-> (o_bus == i_bus2)
    );

    // All ones on i_bus2 must pass i_bus1 through to o_bus.
    check_pass_through_i_bus2: assert property (
        @(posedge clk) (i_bus2 == 8'hFF) |-> (o_bus == i_bus1)
    );

    // If both inputs are stable, the output must remain stable.
    check_stable_output_when_inputs_stable: assert property (
        @(posedge clk) ($stable(i_bus1) && $stable(i_bus2)) |-> $stable(o_bus)
    );

    // A zero on o_bus implies at least one input is zero.
    check_zero_output_implies_zero_input: assert property (
        @(posedge clk) (o_bus == 8'h00) |-> ((i_bus1 == 8'h00) || (i_bus2 == 8'h00))
    );

    // A non-zero output implies both inputs are non-zero.
    check_nonzero_output_implies_nonzero_inputs: assert property (
        @(posedge clk) (o_bus != 8'h00) |-> ((i_bus1 != 8'h00) && (i_bus2 != 8'h00))
    );

endmodule