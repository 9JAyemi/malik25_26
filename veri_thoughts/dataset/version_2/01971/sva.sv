module bidirectional_data_port_sva (
    input  logic        clk,
    input  logic        reset,   // active-high reset (unused by RTL but used to disable assertions)
    input  logic [15:0] in,
    input  logic [15:0] out
);
    ///// Functional mapping /////
    // Out matches the RTL's conditional mapping exactly.
    check_out_function: assert property (
        @(posedge clk) disable iff (reset)
            out == ((in > 16'h7FFF) ? ((~in) + 16'h1) : in)
    );

    // For in <= 0x7FFF, out equals in.
    check_low_half_passthrough: assert property (
        @(posedge clk) disable iff (reset)
            (in <= 16'h7FFF) |-> (out == in)
    );

    // For in > 0x7FFF, out equals two's complement of in.
    check_high_half_twos_complement: assert property (
        @(posedge clk) disable iff (reset)
            (in > 16'h7FFF) |-> (out == ((~in) + 16'h1))
    );

    ///// Boundary and range properties /////
    // For in == 0x8000, out == 0x8000.
    check_boundary_in_8000_out_8000: assert property (
        @(posedge clk) disable iff (reset)
            (in == 16'h8000) |-> (out == 16'h8000)
    );

    // Out[15] is 0 for all inputs except when in == 0x8000.
    check_out_msb_zero_except_8000: assert property (
        @(posedge clk) disable iff (reset)
            (in != 16'h8000) |-> (out[15] == 1'b0)
    );

    // Out never exceeds 0x8000.
    check_out_upper_bound_8000: assert property (
        @(posedge clk) disable iff (reset)
            (out <= 16'h8000)
    );

    // For in > 0x7FFF, in + out wraps to 0 (16-bit).
    check_high_half_sum_zero: assert property (
        @(posedge clk) disable iff (reset)
            (in > 16'h7FFF) |-> ((in + out) == 16'h0000)
    );

    ///// Specific corner cases /////
    // For in == 0x7FFF, out == 0x7FFF.
    check_boundary_7fff_passthrough: assert property (
        @(posedge clk) disable iff (reset)
            (in == 16'h7FFF) |-> (out == 16'h7FFF)
    );

    // For in == 0xFFFF, out == 0x0001.
    check_boundary_ffff_maps_to_one: assert property (
        @(posedge clk) disable iff (reset)
            (in == 16'hFFFF) |-> (out == 16'h0001)
    );

    ///// Consistency /////
    // If in is stable across a cycle, out is stable across that cycle.
    check_stability_with_stable_input: assert property (
        @(posedge clk) disable iff (reset)
            $stable(in) |-> $stable(out)
    );
endmodule