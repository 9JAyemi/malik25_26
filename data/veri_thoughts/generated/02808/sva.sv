module split_16bit_to_8bit_sva (
    input logic [15:0] in,
    input logic [7:0]  out_hi,
    input logic [7:0]  out_lo
);
    ///// Functional checks (sampled on a data edge since no clock/reset in RTL) /////
    // out_hi is always zero because hi_byte truncates to 8'b0 and a bit-select is zero-extended.
    check_out_hi_const_zero: assert property (
        @(posedge in[0]) (out_hi == 8'h00)
    );

    // out_hi remains stable (constant zero).
    check_out_hi_stable: assert property (
        @(posedge in[0]) $stable(out_hi)
    );

    // out_lo[7:1] must always be zero due to zero-extension of a single selected bit.
    check_out_lo_zero_extended: assert property (
        @(posedge in[0]) (out_lo[7:1] == 7'b0)
    );

    // out_lo[0] equals the selected bit from in[3:0] indexed by in[13:12].
    check_out_lo_dynamic_index: assert property (
        @(posedge in[0]) (out_lo[0] == in[in[13:12]])
    );

    // When select_lo==0, out_lo equals {7'b0, in[0]}.
    check_out_lo_sel_case0: assert property (
        @(posedge in[0]) (in[13:12] == 2'd0) |=> (out_lo == {7'b0, in[0]})
    );

    // When select_lo==1, out_lo equals {7'b0, in[1]}.
    check_out_lo_sel_case1: assert property (
        @(posedge in[0]) (in[13:12] == 2'd1) |=> (out_lo == {7'b0, in[1]})
    );

    // When select_lo==2, out_lo equals {7'b0, in[2]}.
    check_out_lo_sel_case2: assert property (
        @(posedge in[0]) (in[13:12] == 2'd2) |=> (out_lo == {7'b0, in[2]})
    );

    // When select_lo==3, out_lo equals {7'b0, in[3]}.
    check_out_lo_sel_case3: assert property (
        @(posedge in[0]) (in[13:12] == 2'd3) |=> (out_lo == {7'b0, in[3]})
    );

    // out_lo can only be 8'h00 or 8'h01 (zero-extended single bit).
    check_out_lo_binary_range: assert property (
        @(posedge in[0]) (out_lo inside {8'h00, 8'h01})
    );

    // If out_lo is 1, the selected input bit must be 1 (same-cycle consistency).
    check_out_lo_one_implies_sel_one: assert property (
        @(posedge in[0]) (out_lo == 8'h01) |=> (in[in[13:12]] == 1'b1)
    );

    // If the selected input bit is 0, out_lo must be 0 (same-cycle consistency).
    check_sel_zero_implies_out_lo_zero: assert property (
        @(posedge in[0]) (in[in[13:12]] == 1'b0) |=> (out_lo == 8'h00)
    );

    // If in[3:0] are all zero, out_lo must be zero for any select.
    check_lower_nibble_zero_implies_out_lo_zero: assert property (
        @(posedge in[0]) (in[3:0] == 4'b0000) |=> (out_lo == 8'h00)
    );

    // Equivalent Boolean form of selection: out_lo equals OR of gated bits, zero-extended.
    check_out_lo_boolean_form: assert property (
        @(posedge in[0])
        out_lo == {7'b0, (((in[13:12]==2'd0) && in[0]) ||
                          ((in[13:12]==2'd1) && in[1]) ||
                          ((in[13:12]==2'd2) && in[2]) ||
                          ((in[13:12]==2'd3) && in[3]))}
    );
endmodule