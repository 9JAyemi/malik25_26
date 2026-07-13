module top_module_sva (
    input  logic        CLK,
    input  logic        RESETn,
    input  logic [15:0] in,
    input  logic [7:0]  out_hi,
    input  logic [7:0]  out_lo,
    input  logic [7:0]  out_sum
);
    // Derived signals mirroring RTL structure
    wire [7:0] in_hi = in[15:8];
    wire [7:0] in_lo = in[7:0];
    wire       sel_hi = in_hi[7];

    // When sel_hi=1, out_hi equals in_hi and out_lo is zero.
    check_out_hi_when_sel: assert property (
        @(posedge CLK) disable iff (!RESETn) sel_hi |-> (out_hi == in_hi) && (out_lo == 8'h00)
    );

    // When sel_hi=0, out_lo equals in_lo and out_hi is zero.
    check_out_lo_when_not_sel: assert property (
        @(posedge CLK) disable iff (!RESETn) !sel_hi |-> (out_lo == in_lo) && (out_hi == 8'h00)
    );

    // out_hi and out_lo are never simultaneously non-zero.
    check_outputs_mutex_nonzero: assert property (
        @(posedge CLK) disable iff (!RESETn) (out_hi == 8'h00) || (out_lo == 8'h00)
    );

    // Bitwise OR of outputs equals the selected byte.
    check_or_matches_selected_byte: assert property (
        @(posedge CLK) disable iff (!RESETn) (out_hi | out_lo) == (sel_hi ? in_hi : in_lo)
    );

    // The MSB of out_hi reflects sel_hi (in[15]).
    check_out_hi_msb_reflects_sel: assert property (
        @(posedge CLK) disable iff (!RESETn) out_hi[7] == sel_hi
    );

    // The MSB of out_lo is masked by ~sel_hi.
    check_out_lo_msb_masking: assert property (
        @(posedge CLK) disable iff (!RESETn) out_lo[7] == ((~sel_hi) & in_lo[7])
    );

    // Bitwise AND of outputs is always zero.
    check_bitwise_and_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (out_hi & out_lo) == 8'h00
    );

    // Because of mutual exclusion, XOR equals OR for outputs.
    check_xor_equals_or_due_mutex: assert property (
        @(posedge CLK) disable iff (!RESETn) (out_hi ^ out_lo) == (out_hi | out_lo)
    );

    // out_sum is the lower 8 bits of in_hi + in_lo.
    check_out_sum_is_byte_sum_lsb: assert property (
        @(posedge CLK) disable iff (!RESETn) out_sum == (in_hi + in_lo)[7:0]
    );

    // If both bytes are zero, out_sum is zero.
    check_out_sum_zero_when_both_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) ((in_hi == 8'h00) && (in_lo == 8'h00)) |-> (out_sum == 8'h00)
    );

    // Example wrap: 0xFF + 0x01 wraps to 0x00 on out_sum.
    check_out_sum_wrap_example: assert property (
        @(posedge CLK) disable iff (!RESETn) ((in_hi == 8'hFF) && (in_lo == 8'h01)) |-> (out_sum == 8'h00)
    );

endmodule