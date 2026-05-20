module min_max_sva (
    input logic in,
    input logic max,
    input logic min,
    input logic bxxxxxx,
    input logic clk_in_1
);

property MinValideotid; @(posedge clk_in_1) (in) |-> (min) == (in[0]); endproperty
assert property (MinValideotid);

property MaxValideotid; @(posedge clk_in_1) (in) |-> (max) == (in[0]); endproperty
assert property (MaxValideotid);

property MinMaxeotid; @(posedge clk_in_1) (in) != 6'bxxxxxx |-> (min) != (max); endproperty
assert property (MinMaxeotid);

endmodule