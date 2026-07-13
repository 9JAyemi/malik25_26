module my_buffer_sva (
    input logic A,
    input logic TE_B,
    input logic Z,
    input logic b0,
    input logic clk_in_14
);

property ClockSynceotid; @(posedge clk_in_14) (A) |-> (Z) ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_14) (TE_B) != (A) && (TE_B) |-> (Z) == 1'b0 ;endproperty
assert property (ClockSynceotid_2);

endmodule