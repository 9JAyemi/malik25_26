module counter_sva (
    input logic       clk,
    input logic [2:0] count
);

    // 000 advances to 001.
    check_count_000_to_001: assert property (
        @(posedge clk) (count == 3'b000) |=> (count == 3'b001)
    );

    // 001 advances to 010.
    check_count_001_to_010: assert property (
        @(posedge clk) (count == 3'b001) |=> (count == 3'b010)
    );

    // 010 advances to 011.
    check_count_010_to_011: assert property (
        @(posedge clk) (count == 3'b010) |=> (count == 3'b011)
    );

    // 011 advances to 100.
    check_count_011_to_100: assert property (
        @(posedge clk) (count == 3'b011) |=> (count == 3'b100)
    );

    // 100 advances to 101.
    check_count_100_to_101: assert property (
        @(posedge clk) (count == 3'b100) |=> (count == 3'b101)
    );

    // 101 advances to 110.
    check_count_101_to_110: assert property (
        @(posedge clk) (count == 3'b101) |=> (count == 3'b110)
    );

    // 110 advances to 111.
    check_count_110_to_111: assert property (
        @(posedge clk) (count == 3'b110) |=> (count == 3'b111)
    );

    // 111 wraps back to 000.
    check_count_111_to_000: assert property (
        @(posedge clk) (count == 3'b111) |=> (count == 3'b000)
    );

endmodule