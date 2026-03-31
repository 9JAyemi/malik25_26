module fifo_wp_inc_sva (
    input logic clk,
    input logic free2,
    input logic free3,
    input logic [1:0] tm_count,
    input logic [3:0] fifowp_inc
);

    // free3 with tm_count of 3 selects increment 3.
    check_free3_tm3_increment3: assert property (
        @(posedge clk)
        (free3 && (tm_count == 2'b11)) |-> (fifowp_inc == 4'b0011)
    );

    // free2 with tm_count of 2 or 3 selects increment 2 when the free3 case is absent.
    check_free2_high_count_increment2: assert property (
        @(posedge clk)
        (!(free3 && (tm_count == 2'b11)) && free2 && (tm_count >= 2'b10)) |-> (fifowp_inc == 4'b0010)
    );

    // Any remaining nonzero tm_count selects increment 1.
    check_fallback_nonzero_count_increment1: assert property (
        @(posedge clk)
        (!(free3 && (tm_count == 2'b11)) &&
         !(free2 && (tm_count >= 2'b10)) &&
         (tm_count >= 2'b01)) |-> (fifowp_inc == 4'b0001)
    );

    // tm_count of 0 selects increment 0.
    check_zero_count_increment0: assert property (
        @(posedge clk)
        (tm_count == 2'b00) |-> (fifowp_inc == 4'b0000)
    );

    // Output 3 only occurs for free3 with tm_count of 3.
    check_increment3_condition: assert property (
        @(posedge clk)
        (fifowp_inc == 4'b0011) |-> (free3 && (tm_count == 2'b11))
    );

    // Output 2 only occurs for the second branch condition.
    check_increment2_condition: assert property (
        @(posedge clk)
        (fifowp_inc == 4'b0010) |-> (!(free3 && (tm_count == 2'b11)) && free2 && (tm_count >= 2'b10))
    );

    // Output 1 only occurs for the third branch condition.
    check_increment1_condition: assert property (
        @(posedge clk)
        (fifowp_inc == 4'b0001) |-> (!(free3 && (tm_count == 2'b11)) &&
                                     !(free2 && (tm_count >= 2'b10)) &&
                                     (tm_count >= 2'b01))
    );

    // Output 0 only occurs when tm_count is 0.
    check_increment0_condition: assert property (
        @(posedge clk)
        (fifowp_inc == 4'b0000) |-> (tm_count == 2'b00)
    );

endmodule