module top_module_sva (
    input logic A,
    input logic B,
    input logic SEL,
    input logic clk,
    input logic result,
    input logic shift_out
);

property AddSynceotid; @(posedge clk) (SEL[1]) |-> result == shift_out ; endproperty
assert property (AddSynceotid);

property AddSynceotid_2; @(posedge clk) (SEL[1]) |->  (  (  A  -  B  )  ==  result  ) ; endproperty
assert property (AddSynceotid_2);

property AddSynceotid_3; @(posedge clk) ( ! SEL[1] )  |->  (  (  A  +  B  )  ==  result  ) ; endproperty
assert property (AddSynceotid_3);

endmodule