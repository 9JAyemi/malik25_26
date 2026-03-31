module fifo_wp_inc_sva (
    input logic clk,
    input logic free2,
    input logic free3,
    input logic [1:0] tm_count,
    input logic [3:0] fifowp_inc
);

    // free3 and tm_count 11 select 0011.
    check_free3_tm11: assert property (
        @(posedge clk) (free3 && (tm_count == 2'b11)) |-> (fifowp_inc == 4'b0011)
    );

    // free2 and tm_count 10 select 0010.
    check_free2_tm10: assert property (
        @(posedge clk) (free2 && (tm_count == 2'b10)) |-> (fifowp_inc == 4'b0010)
    );

    // free2 and tm_count 01 select 0010.
    check_free2_tm01: assert property (
        @(posedge clk) (free2 && (tm_count == 2'b01)) |-> (fifowp_inc == 4'b0010)
    );

    // free2 and tm_count 00 select 0000.
    check_free2_tm00: assert property (
        @(posedge clk) (free2 && (tm_count == 2'b00)) |-> (fifowp_inc == 4'b0000)
    );

    // No free and tm_count 11 select 0000.
    check_no_free_tm11: assert property (
        @(posedge clk) ((!free3) && (tm_count == 2'b11)) |-> (fifowp_inc == 4'b0000)
    );

    // No free and tm_count 10 select 0000.
    check_no_free_tm10: assert property (
        @(posedge clk) ((!free3) && (tm_count == 2'b10)) |-> (fifowp_inc == 4'b0000)
    );

    // No free and tm_count 01 select 0001.
    check_no_free_tm01: assert property (
        @(posedge clk) ((!free3) && (tm_count == 2'b01)) |-> (fifowp_inc == 4'b0001)
    );

    // No free and tm_count 00 select 0000.
    check_no_free_tm00: assert property (
        @(posedge clk) ((!free3) && (tm_count == 2'b00)) |-> (fifowp_inc == 4'b0000)
    );

    // free3 has priority over free2 when both are asserted.
    check_free3_priority: assert property (
        @(posedge clk) (free3 && free2 && (tm_count == 2'b11)) |-> (fifowp_inc == 4'b0011)
    );

    // free2 has priority over tm_count 01 when free3 is low.
    check_free2_priority: assert property (
        @(posedge clk) ((!free3) && free2 && (tm_count == 2'b01)) |-> (fifowp_inc == 4'b0010)
    );

endmodule