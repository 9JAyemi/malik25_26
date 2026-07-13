module top_module_sva (
    input logic CLK,               // Sampling clock for assertions (DUT has no clock)
    input logic [15:0] in,
    input logic [11:0] out
);
    // DUT has no reset; purely combinational

    // Upper 4 bits of out are always zero.
    check_out_upper_zero: assert property (
        @(posedge CLK) out[11:8] == 4'b0000
    );

    // Lower 8 bits equal upper byte AND NOT lower byte.
    check_out_lower_eq_hi_and_not_lo: assert property (
        @(posedge CLK) out[7:0] == (in[15:8] & ~in[7:0])
    );

    // Lower 8 bits equal upper byte AND (upper XOR lower).
    check_out_lower_eq_hi_and_xor: assert property (
        @(posedge CLK) out[7:0] == (in[15:8] & (in[15:8] ^ in[7:0]))
    );

    // Output bits are a subset of the upper input byte.
    check_out_subset_of_hi: assert property (
        @(posedge CLK) (out[7:0] & ~in[15:8]) == 8'h00
    );

    // No output bit is set where the lower input byte has a 1.
    check_out_disjoint_with_lo: assert property (
        @(posedge CLK) (out[7:0] & in[7:0]) == 8'h00
    );

    // If the upper byte is zero, the entire output is zero.
    check_hi_zero_implies_out_zero: assert property (
        @(posedge CLK) (in[15:8] == 8'h00) |-> (out == 12'h000)
    );

    // If the lower byte is all ones, the entire output is zero.
    check_lo_ones_implies_out_zero: assert property (
        @(posedge CLK) (in[7:0] == 8'hFF) |-> (out == 12'h000)
    );

    // If the lower byte is zero, the lower output equals the upper byte.
    check_lo_zero_implies_out_eq_hi: assert property (
        @(posedge CLK) (in[7:0] == 8'h00) |-> ((out[7:0] == in[15:8]) && (out[11:8] == 4'b0000))
    );

    // If upper and lower bytes are equal, the output is zero.
    check_equal_bytes_implies_out_zero: assert property (
        @(posedge CLK) (in[15:8] == in[7:0]) |-> (out == 12'h000)
    );

    // If input is stable across a cycle, output is stable across the cycle.
    check_stability_when_input_stable: assert property (
        @(posedge CLK) $stable(in) |-> $stable(out)
    );
endmodule