module mux_2to1_sva (
    input logic clk,
    input logic i0,
    input logic i1,
    input logic s,
    input logic z
);

    // Output always matches the 2-to-1 mux function.
    check_mux_function: assert property (
        @(posedge clk) z === (s ? i1 : i0)
    );

    // When select is low, the output is i0.
    check_select_low: assert property (
        @(posedge clk) !s |-> (z === i0)
    );

    // When select is high, the output is i1.
    check_select_high: assert property (
        @(posedge clk) s |-> (z === i1)
    );

    // If inputs and select are unchanged, the output is unchanged.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({i0, i1, s}) |-> $stable(z)
    );

endmodule

module mux32bit_2to1_sva (
    input logic clk,
    input logic [31:0] i0,
    input logic [31:0] i1,
    input logic s,
    input logic [31:0] z
);

    // Output always matches the 32-bit 2-to-1 mux function.
    check_mux_function_32: assert property (
        @(posedge clk) z === (s ? i1 : i0)
    );

    // When select is low, the output is i0.
    check_select_low_32: assert property (
        @(posedge clk) !s |-> (z === i0)
    );

    // When select is high, the output is i1.
    check_select_high_32: assert property (
        @(posedge clk) s |-> (z === i1)
    );

    // If inputs and select are unchanged, the output is unchanged.
    check_output_stable_when_inputs_stable_32: assert property (
        @(posedge clk) $stable({i0, i1, s}) |-> $stable(z)
    );

endmodule