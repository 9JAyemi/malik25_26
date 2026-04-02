module fifo_wp_inc_sva (
    input logic clk,
    input logic rst_n,
    input logic free2,
    input logic free3,
    input logic [1:0] tm_count,
    output logic [3:0] fifowp_inc
);
    // Sequential logic, so use @(posedge clk) for assertions

    // Check that fifowp_inc is set to 4'b0011 when free3 is high and tm_count is 2'b11
    fifo_wp_inc_1: assert property (
        @(posedge clk) disable iff (!rst_n) (free3 && (tm_count == 2'b11)) |-> (fifowp_inc == 4'b0011)
    );

    // Check that fifowp_inc is set to 4'b0010 when free2 is high and tm_count is 2'b10 or higher
    fifo_wp_inc_2: assert property (
        @(posedge clk) disable iff (!rst_n) (free2 && (tm_count >= 2'b10)) |-> (fifowp_inc == 4'b0010)
    );

    // Check that fifowp_inc is set to 4'b0001 when tm_count is 2'b01 or higher
    fifo_wp_inc_3: assert property (
        @(posedge clk) disable iff (!rst_n) (tm_count >= 2'b01) |-> (fifowp_inc == 4'b0001)
    );

    // Check that fifowp_inc is set to 4'b0000 when tm_count is 2'b00
    fifo_wp_inc_4: assert property (
        @(posedge clk) disable iff (!rst_n) (tm_count == 2'b00) |-> (fifowp_inc == 4'b0000)
    );

    // Check that fifowp_inc is reset to 4'b0000 at reset
    fifo_wp_inc_5: assert property (
        @(posedge clk) disable iff (!rst_n) rst_n |-> (fifowp_inc == 4'b0000)
    );

endmodule