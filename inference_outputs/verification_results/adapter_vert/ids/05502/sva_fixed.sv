module signal_converter_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    input logic VGND,
    input logic VNB,
    input logic VPB,
    input logic VPWR,
    input logic b1,
    input logic clk_signal_18
);

property PowerOnCheckeotid; @(posedge clk_signal_18) (A1) && (A2) && (A3) |-> (VPWR) && !(VGND) && (VPB) && !(VNB) ;endproperty
assert property (PowerOnCheckeotid);

property ValidDataeotid; @(posedge clk_signal_18) (A1) && (A2) && (A3) || (A1) && (A2) && (B1) || (A1) && (A2) && (C1) || (A1) && (A3) && (B1) || (A1) && (A3) && (C1) || (A2) && (A3) && (B1) || (A2) && (A3) && (C1) || (A2) && (B1) && (C1) || (A3) && (B1) && (C1)  == 1'b1 ;endproperty
assert property (ValidDataeotid);

endmodule