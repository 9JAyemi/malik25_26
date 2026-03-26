module sync_ptr_sva #(
    parameter ASIZE = 4
)(
    input logic              dest_clk,
    input logic              dest_rst_n,
    input logic [ASIZE:0]    src_ptr,
    input logic [ASIZE:0]    dest_ptr
);

    // Active-low reset clears the synchronized pointer.
    check_reset_clears_dest_ptr: assert property (
        @(posedge dest_clk)
        !dest_rst_n |-> (dest_ptr == '0)
    );

    // The first dest_clk after a sampled low reset still outputs zero.
    check_prev_reset_keeps_output_zero: assert property (
        @(posedge dest_clk) disable iff (!dest_rst_n)
        ($past(dest_rst_n,1) == 1'b0) |-> (dest_ptr == '0)
    );

    // With reset sampled high on consecutive clocks, output is prior src_ptr or zero.
    check_output_is_prev_src_or_zero: assert property (
        @(posedge dest_clk) disable iff (!dest_rst_n)
        ($past(dest_rst_n,1) == 1'b1) |-> ((dest_ptr == $past(src_ptr,1)) || (dest_ptr == '0))
    );

    // A nonzero output must match the previous sampled source pointer.
    check_nonzero_output_matches_prev_src: assert property (
        @(posedge dest_clk) disable iff (!dest_rst_n)
        (($past(dest_rst_n,1) == 1'b1) && (dest_ptr != '0)) |-> (dest_ptr == $past(src_ptr,1))
    );

    // A zero source sample propagates to a zero output on the next clock.
    check_zero_source_propagates: assert property (
        @(posedge dest_clk) disable iff (!dest_rst_n)
        (($past(dest_rst_n,1) == 1'b1) && ($past(src_ptr,1) == '0)) |-> (dest_ptr == '0)
    );

endmodule