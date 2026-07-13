module odd_even_sva (
    input logic input_bits,
    input logic output_bits,
    input logic b01,
    input logic b10,
    input logic clk_in_1
);

property OddCheckeotid; @(posedge clk_in_1) (input_bits[0] == 1) |-> output_bits == 2'b01 ; endproperty
assert property (OddCheckeotid);

property EvenCheckeotid; @(posedge clk_in_1) (input_bits[0] != 1) |-> output_bits == 2'b10 ; endproperty
assert property (EvenCheckeotid);

endmodule