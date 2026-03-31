module axi_timer_sva (
    input logic clk,
    input logic [4:0] bus2ip_addr_i_reg,
    input logic Q,
    input logic ce_expnd_i_5
);

// Address 0000 with Q low drives ce_expnd_i_5 low.
    check_addr_0000_q0_low: assert property (
        @(posedge clk) (bus2ip_addr_i_reg == 5'd0 && Q == 1'b0) |-> (ce_expnd_i_5 == 1'b0)
    );

// Address 0000 with Q high drives ce_expnd_i_5 low.
    check_addr_0000_q1_low: assert property (
        @(posedge clk) (bus2ip_addr_i_reg == 5'd0 && Q == 1'b1) |-> (ce_expnd_i_5 == 1'b0)
    );

// Address 0001 drives ce_expnd_i_5 low.
    check_addr_0001_low: assert property (
        @(posedge clk) (bus2ip_addr_i_reg == 5'd1) |-> (ce_expnd_i_5 == 1'b0)
    );

// Address 0010 drives ce_expnd_i_5 low.
    check_addr_0010_low: assert property (
        @(posedge clk) (bus2ip_addr_i_reg == 5'd2) |-> (ce_expnd_i_5 == 1'b0)
    );

// Address 0011 drives ce_expnd_i_5 low.
    check_addr_0011_low: assert property (
        @(posedge clk) (bus2ip_addr_i_reg == 5'd3) |-> (ce_expnd_i_5 == 1'b0)
    );

// Address 0100 drives ce_expnd_i_5 low.
    check_addr_0100_low: assert property (
        @(posedge clk) (bus2ip_addr_i_reg == 5'd4) |-> (ce_expnd_i_5 == 1'b0)
    );

// Address 0101 drives ce_expnd_i_5 low.
    check_addr_0101_low: assert property (
        @(posedge clk) (bus2ip_addr_i_reg == 5'd5) |-> (ce_expnd_i_5 == 1'b0)
    );

// Address 0110 drives ce_expnd_i_5 low.
    check_addr_0110_low: assert property (
        @(posedge clk) (bus2ip_addr_i_reg == 5'd6) |-> (ce_expnd_i_5 == 1'b0)
    );

// Address 0111 drives ce_expnd_i_5 low.
    check_addr_0111_low: assert property (
        @(posedge clk) (bus2ip_addr_i_reg == 5'd7) |-> (ce_expnd_i_5 == 1'b0)
    );

// Address 1000 drives ce_expnd_i_5 high.
    check_addr_1000_high: assert property (
        @(posedge clk) (bus2ip_addr_i_reg == 5'd8) |-> (ce_expnd_i_5 == 1'b1)
    );

// Address 1001 drives ce_expnd_i_5 low.
    check_addr_1001_low: assert property (
        @(posedge clk) (bus2ip_addr_i_reg == 5'd9) |-> (ce_expnd_i_5 == 1'b0)
    );

// Address 1010 drives ce_expnd_i_5 low.
    check_addr_1010_low: assert property (
        @(posedge clk) (bus2ip_addr_i_reg == 5'd10) |-> (ce_expnd_i_5 == 1'b0)
    );

// Address 1011 drives ce_expnd_i_5 low.
    check_addr_1011_low: assert property (
        @(posedge clk) (bus2ip_addr_i_reg == 5'd11) |-> (ce_expnd_i_5 == 1'b0)
    );

// Address 1100 drives ce_expnd_i_5 low.
    check_addr_1100_low: assert property (
        @(posedge clk) (bus2ip_addr_i_reg == 5'd12) |-> (ce_expnd_i_5 == 1'b0)
    );

// Address 1101 drives ce_expnd_i_5 low.
    check_addr_1101_low: assert property (
        @(posedge clk) (bus2ip_addr_i_reg == 5'd13) |-> (ce_expnd_i_5 == 1'b0)
    );

// Address 1110 drives ce_expnd_i_5 low.
    check_addr_1110_low: assert property (
        @(posedge clk) (bus2ip_addr_i_reg == 5'd14) |-> (ce_expnd_i_5 == 1'b0)
    );

// Address 1111 drives ce_expnd_i_5 low.
    check_addr_1111_low: assert property (
        @(posedge clk) (bus2ip_addr_i_reg == 5'd15) |-> (ce_expnd_i_5 == 1'b0)
    );

endmodule
