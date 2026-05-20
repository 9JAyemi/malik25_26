module OAI21X1_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic Y,
    input logic clk_osc_14
);

property ORANDeotid; @(posedge clk_osc_14) ( A ) |->  ( Y  != (  A  |  B  ) &  C  );endproperty
assert property (ORANDeotid);

property ORANDeotid_2; @(posedge clk_osc_14) ( B ) |->  ( Y  != (  A  |  B  ) &  C  );endproperty
assert property (ORANDeotid_2);

property ANDeotid; @(posedge clk_osc_14) ( C ) |->  ( Y  ==  (  A  |  B  ) &  C  );endproperty
assert property (ANDeotid);

endmodule