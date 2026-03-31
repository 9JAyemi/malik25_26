module fifo_wp_inc_sva (
    input logic clk,
    input logic free2,
    input logic free3,
    input logic [1:0] tm_count,
    input logic [3:0] fifowp_inc
);

    // free3 with tm_count 3 returns 0011.
    check_free3_tm3: assert property (
        @(posedge clk) (free3 && (tm_count == 2'b11)) |-> (fifowp_inc == 4'b0011)
    );

    // free3 with tm_count 2 returns 0011.
    check_free3_tm2: assert property (
        @(posedge clk) (free3 && (tm_count == 2'b10)) |-> (fifowp_inc == 4'b0011)
    );

    // free2 with tm_count 2 returns 0010.
    check_free2_tm2: assert property (
        @(posedge clk) (free2 && (tm_count == 2'b10)) |-> (fifowp_inc == 4'b0010)
    );

    // free2 with tm_count 1 returns 0001.
    check_free2_tm1: assert property (
        @(posedge clk) (free2 && (tm_count == 2'b01)) |-> (fifowp_inc == 4'b0001)
    );

    // tm_count 0 returns 0000.
    check_tm0: assert property (
        @(posedge clk) (tm_count == 2'b00) |-> (fifowp_inc == 4'b0000)
    );

    // tm_count 1 returns 0001.
    check_tm1: assert property (
        @(posedge clk) (tm_count == 2'b01) |-> (fifowp_inc == 4'b0001)
    );

    // tm_count 2 returns 0010.
    check_tm2: assert property (
        @(posedge clk) (tm_count == 2'b10) |-> (fifowp_inc == 4'b0010)
    );

    // tm_count 3 returns 0011.
    check_tm3: assert property (
        @(posedge clk) (tm_count == 2'b11) |-> (fifowp_inc == 4'b0011)
    );

    // free3 has priority over free2 when both are asserted.
    check_free3_priority: assert property (
        @(posedge clk) (free3 && free2 && (tm_count == 2'b11)) |-> (fifowp_inc == 4'b0011)
    );

    // free2 has priority over tm_count 1 when free3 is low.
    check_free2_priority: assert property (
        @(posedge clk) (free2 && (tm_count == 2'b01)) |-> (fifowp_inc == 4'b0010)
    );

    // tm_count 1 has priority over tm_count 0 when free2 and free3 are low.
    check_tm1_priority: assert property (
        @(posedge clk) ((tm_count == 2'b01) && !free2 && !free3) |-> (fifowp_inc == 4'b0001)
    );

endmodule