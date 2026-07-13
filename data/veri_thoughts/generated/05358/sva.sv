module gray_code_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] gray_out
);

    // Reset drives gray_out to 0000 on the following clock.
    check_reset_drives_zero: assert property (
        @(posedge clk) rst |=> (gray_out == 4'b0000)
    );

    // 0000 advances to 0001.
    check_gray_0000_to_0001: assert property (
        @(posedge clk) disable iff (rst) (gray_out == 4'b0000) |=> (gray_out == 4'b0001)
    );

    // 0001 advances to 0011.
    check_gray_0001_to_0011: assert property (
        @(posedge clk) disable iff (rst) (gray_out == 4'b0001) |=> (gray_out == 4'b0011)
    );

    // 0011 advances to 0010.
    check_gray_0011_to_0010: assert property (
        @(posedge clk) disable iff (rst) (gray_out == 4'b0011) |=> (gray_out == 4'b0010)
    );

    // 0010 advances to 0110.
    check_gray_0010_to_0110: assert property (
        @(posedge clk) disable iff (rst) (gray_out == 4'b0010) |=> (gray_out == 4'b0110)
    );

    // 0110 advances to 0111.
    check_gray_0110_to_0111: assert property (
        @(posedge clk) disable iff (rst) (gray_out == 4'b0110) |=> (gray_out == 4'b0111)
    );

    // 0111 advances to 0101.
    check_gray_0111_to_0101: assert property (
        @(posedge clk) disable iff (rst) (gray_out == 4'b0111) |=> (gray_out == 4'b0101)
    );

    // 0101 advances to 0100.
    check_gray_0101_to_0100: assert property (
        @(posedge clk) disable iff (rst) (gray_out == 4'b0101) |=> (gray_out == 4'b0100)
    );

    // 0100 advances to 1100.
    check_gray_0100_to_1100: assert property (
        @(posedge clk) disable iff (rst) (gray_out == 4'b0100) |=> (gray_out == 4'b1100)
    );

    // 1100 advances to 1101.
    check_gray_1100_to_1101: assert property (
        @(posedge clk) disable iff (rst) (gray_out == 4'b1100) |=> (gray_out == 4'b1101)
    );

    // 1101 advances to 1111.
    check_gray_1101_to_1111: assert property (
        @(posedge clk) disable iff (rst) (gray_out == 4'b1101) |=> (gray_out == 4'b1111)
    );

    // 1111 advances to 1110.
    check_gray_1111_to_1110: assert property (
        @(posedge clk) disable iff (rst) (gray_out == 4'b1111) |=> (gray_out == 4'b1110)
    );

    // 1110 advances to 1010.
    check_gray_1110_to_1010: assert property (
        @(posedge clk) disable iff (rst) (gray_out == 4'b1110) |=> (gray_out == 4'b1010)
    );

    // 1010 advances to 1011.
    check_gray_1010_to_1011: assert property (
        @(posedge clk) disable iff (rst) (gray_out == 4'b1010) |=> (gray_out == 4'b1011)
    );

    // 1011 advances to 1001.
    check_gray_1011_to_1001: assert property (
        @(posedge clk) disable iff (rst) (gray_out == 4'b1011) |=> (gray_out == 4'b1001)
    );

    // 1001 advances to 1000.
    check_gray_1001_to_1000: assert property (
        @(posedge clk) disable iff (rst) (gray_out == 4'b1001) |=> (gray_out == 4'b1000)
    );

    // 1000 wraps to 0000.
    check_gray_1000_to_0000: assert property (
        @(posedge clk) disable iff (rst) (gray_out == 4'b1000) |=> (gray_out == 4'b0000)
    );

endmodule