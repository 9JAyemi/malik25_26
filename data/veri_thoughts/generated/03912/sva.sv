module message_rom_sva (
    input logic clk,
    input logic [3:0] addr,
    input logic [7:0] data
);

    // Address 0 returns 'H' on the next clock.
    check_addr_0_returns_H: assert property (
        @(posedge clk) (addr == 4'd0) |=> (data == 8'h48)
    );

    // Address 1 returns 'e' on the next clock.
    check_addr_1_returns_e: assert property (
        @(posedge clk) (addr == 4'd1) |=> (data == 8'h65)
    );

    // Address 2 returns 'l' on the next clock.
    check_addr_2_returns_l: assert property (
        @(posedge clk) (addr == 4'd2) |=> (data == 8'h6c)
    );

    // Address 3 returns 'l' on the next clock.
    check_addr_3_returns_l: assert property (
        @(posedge clk) (addr == 4'd3) |=> (data == 8'h6c)
    );

    // Address 4 returns 'o' on the next clock.
    check_addr_4_returns_o: assert property (
        @(posedge clk) (addr == 4'd4) |=> (data == 8'h6f)
    );

    // Address 5 returns space on the next clock.
    check_addr_5_returns_space: assert property (
        @(posedge clk) (addr == 4'd5) |=> (data == 8'h20)
    );

    // Address 6 returns 'W' on the next clock.
    check_addr_6_returns_W: assert property (
        @(posedge clk) (addr == 4'd6) |=> (data == 8'h57)
    );

    // Address 7 returns 'o' on the next clock.
    check_addr_7_returns_o: assert property (
        @(posedge clk) (addr == 4'd7) |=> (data == 8'h6f)
    );

    // Address 8 returns 'r' on the next clock.
    check_addr_8_returns_r: assert property (
        @(posedge clk) (addr == 4'd8) |=> (data == 8'h72)
    );

    // Address 9 returns 'l' on the next clock.
    check_addr_9_returns_l: assert property (
        @(posedge clk) (addr == 4'd9) |=> (data == 8'h6c)
    );

    // Address 10 returns 'd' on the next clock.
    check_addr_10_returns_d: assert property (
        @(posedge clk) (addr == 4'd10) |=> (data == 8'h64)
    );

    // Address 11 returns '!' on the next clock.
    check_addr_11_returns_bang: assert property (
        @(posedge clk) (addr == 4'd11) |=> (data == 8'h21)
    );

    // Address 12 returns newline on the next clock.
    check_addr_12_returns_lf: assert property (
        @(posedge clk) (addr == 4'd12) |=> (data == 8'h0a)
    );

    // Address 13 returns carriage return on the next clock.
    check_addr_13_returns_cr: assert property (
        @(posedge clk) (addr == 4'd13) |=> (data == 8'h0d)
    );

    // Out-of-range addresses return space on the next clock.
    check_addr_out_of_range_returns_space: assert property (
        @(posedge clk) (addr > 4'd13) |=> (data == 8'h20)
    );

endmodule