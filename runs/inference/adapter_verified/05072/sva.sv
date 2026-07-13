module fifo_wp_inc_sva (
    input logic clk,
    input logic free2,
    input logic free3,
    input logic [1:0] tm_count,
    input logic [3:0] fifowp_inc
);

// free3 with tm_count==3 selects 0011.
    check_free3_tm3: assert property (
        @(posedge clk) (free3 && (tm_count == 2'b11)) |-> (fifowp_inc == 4'b0011)
    );

// free3 with tm_count==2 selects 0011.
    check_free3_tm2: assert property (
        @(posedge clk) (free3 && (tm_count == 2'b10)) |-> (fifowp_inc == 4'b0011)
    );

// free2 with tm_count>=2 selects 0010.
    check_free2_tmge2: assert property (
        @(posedge clk) (free2 && (tm_count >= 2'b10)) |-> (fifowp_inc == 4'b0010)
    );

// tm_count>=1 with no free2 selects 0001.
    check_tmge1_no_free2: assert property (
        @(posedge clk) ((!free2) && (tm_count >= 2'b01)) |-> (fifowp_inc == 4'b0001)
    );

// tm_count==0 selects 0000.
    check_tm0: assert property (
        @(posedge clk) (tm_count == 2'b00) |-> (fifowp_inc == 4'b0000)
    );

// tm_count==1 selects 0000.
    check_tm1: assert property (
        @(posedge clk) (tm_count == 2'b01) |-> (fifowp_inc == 4'b0000)
    );

// free2 with tm_count==0 selects 0000.
    check_free2_tm0: assert property (
        @(posedge clk) (free2 && (tm_count == 2'b00)) |-> (fifowp_inc == 4'b0000)
    );

// free2 with tm_count==1 selects 0000.
    check_free2_tm1: assert property (
        @(posedge clk) (free2 && (tm_count == 2'b01)) |-> (fifowp_inc == 4'b0000)
    );

// free3 with tm_count==0 selects 0000.
    check_free3_tm0: assert property (
        @(posedge clk) (free3 && (tm_count == 2'b00)) |-> (fifowp_inc == 4'b0000)
    );

// free3 with tm_count==1 selects 0000.
    check_free3_tm1: assert property (
        @(posedge clk) (free3 && (tm_count == 2'b01)) |-> (fifowp_inc == 4'b0000)
    );

endmodule
