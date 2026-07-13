module and_module_sva (
    input logic        clk,
    input logic [7:0]  i_bus1,
    input logic [7:0]  i_bus2,
    input logic [7:0]  o_bus
);

// o_bus equals bitwise AND of i_bus1 and i_bus2.
    check_and_function: assert property (
        @(posedge clk) o_bus == (i_bus1 & i_bus2)
    );

// If i_bus1 is all zeros, o_bus must be all zeros.
    check_zero_when_i1_zero: assert property (
        @(posedge clk) (i_bus1 == 8'h00) |-> (o_bus == 8'h00)
    );

// If i_bus2 is all zeros, o_bus must be all zeros.
    check_zero_when_i2_zero: assert property (
        @(posedge clk) (i_bus2 == 8'h00) |-> (o_bus == 8'h00)
    );

// If i_bus1 is all ones, o_bus equals i_bus2.
    check_passthrough_when_i1_all_ones: assert property (
        @(posedge clk) (i_bus1 == 8'hFF) |-> (o_bus == i_bus2)
    );

// If i_bus2 is all ones, o_bus equals i_bus1.
    check_passthrough_when_i2_all_ones: assert property (
        @(posedge clk) (i_bus2 == 8'hFF) |-> (o_bus == i_bus1)
    );

// If o_bus is all ones, both inputs must be all ones.
    check_all_ones_implies_inputs_all_ones: assert property (
        @(posedge clk) (o_bus == 8'hFF) |-> ((i_bus1 == 8'hFF) && (i_bus2 == 8'hFF))
    );

// If o_bus has a zero bit, at least one input must have a zero in that bit.
    check_zero_bit_implies_input_zero: assert property (
        @(posedge clk) (|o_bus == 1'b0) |-> ((|i_bus1 == 1'b0) || (|i_bus2 == 1'b0))
    );

endmodule
