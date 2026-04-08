module top_module_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [7:0]  out_hi,
    input logic [7:0]  out_lo
);

    // out_hi always reflects the upper input byte.
    check_out_hi_matches_upper_byte: assert property (
        @(posedge clk) out_hi === in[15:8]
    );

    // out_lo matches the RTL conditional selection.
    check_out_lo_matches_rtl_expression: assert property (
        @(posedge clk) out_lo === ((in[7:0] == 8'b0) ? in[7:0] : in[15:8])
    );

    // A zero upper byte produces a zero out_hi.
    check_zero_upper_byte_drives_zero_out_hi: assert property (
        @(posedge clk) (in[15:8] === 8'h00) |-> (out_hi === 8'h00)
    );

    // A zero lower byte produces a zero out_lo.
    check_zero_lower_byte_drives_zero_out_lo: assert property (
        @(posedge clk) (in[7:0] === 8'h00) |-> (out_lo === 8'h00)
    );

    // A known nonzero lower byte makes out_lo select the upper byte.
    check_nonzero_lower_byte_selects_upper_for_out_lo: assert property (
        @(posedge clk) (!$isunknown(in[7:0]) && (in[7:0] != 8'h00)) |-> (out_lo === in[15:8])
    );

endmodule