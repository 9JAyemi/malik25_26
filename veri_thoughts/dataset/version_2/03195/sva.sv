module NIOS_Sys_nios2_qsys_0_nios2_oci_fifocount_inc_sva (
    input logic clk,
    input logic empty,
    input logic free2,
    input logic free3,
    input logic [1:0] tm_count,
    input logic [4:0] fifocount_inc
);

    // Sample clock for this combinational DUT; RTL has no reset.
    
    // When empty is high, the output mirrors tm_count with zero extension.
    check_empty_passthrough: assert property (
        @(posedge clk)
        empty |-> (fifocount_inc == {3'b000, tm_count})
    );

    // When not empty and tm_count is 0, the output is all ones.
    check_nonempty_tm_count_0: assert property (
        @(posedge clk)
        (!empty && (tm_count == 2'd0)) |-> (fifocount_inc == 5'b11111)
    );

    // When not empty and tm_count is 1, the output is zero.
    check_nonempty_tm_count_1: assert property (
        @(posedge clk)
        (!empty && (tm_count == 2'd1)) |-> (fifocount_inc == 5'd0)
    );

    // When not empty and tm_count is 2, free2 selects between 1 and 0.
    check_nonempty_tm_count_2: assert property (
        @(posedge clk)
        (!empty && (tm_count == 2'd2)) |-> (fifocount_inc == (free2 ? 5'd1 : 5'd0))
    );

    // When not empty and tm_count is 3, free3 has priority over free2.
    check_nonempty_tm_count_3: assert property (
        @(posedge clk)
        (!empty && (tm_count == 2'd3)) |-> (fifocount_inc == (free3 ? 5'd2 : (free2 ? 5'd1 : 5'd0)))
    );

endmodule