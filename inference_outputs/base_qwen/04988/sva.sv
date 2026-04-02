module calculator_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] add,
    input logic [3:0] sub,
    input logic [3:0] mul,
    input logic [3:0] div
);
    // 4-bit adder
    adder_check: assert property (
        @(posedge clk) disable iff (!RESETn) (add == A + B)
    ) else $error("Adder output is incorrect");

    // 4-bit subtractor
    subtractor_check: assert property (
        @(posedge clk) disable iff (!RESETn) (sub == A - B)
    ) else $error("Subtractor output is incorrect");

    // 4-bit multiplier
    multiplier_check: assert property (
        @(posedge clk) disable iff (!RESETn) (mul == A * B)
    ) else $error("Multiplier output is incorrect");

    // 4-bit divider
    divider_check: assert property (
        @(posedge clk) disable iff (!RESETn) (div == A / B)
    ) else $error("Divider output is incorrect");
endmodule