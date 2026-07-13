module bit_counter_sva (
    input logic clk,
    input logic [2:0] data,
    input logic [1:0] count
);

    // count must match the implemented reduction-NAND expression.
    check_count_matches_expression: assert property (
        @(posedge clk) count == {(~&data[2:1]), (~&data[1:0])}
    );

    // count[1] must be the NAND reduction of data[2:1].
    check_count_msb_definition: assert property (
        @(posedge clk) count[1] == (~&data[2:1])
    );

    // count[0] must be the NAND reduction of data[1:0].
    check_count_lsb_definition: assert property (
        @(posedge clk) count[0] == (~&data[1:0])
    );

endmodule