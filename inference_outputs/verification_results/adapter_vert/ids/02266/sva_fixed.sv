module simple_calculator_sva (
    input logic A,
    input logic B,
    input logic CLK,
    input logic C_reg,
    input logic OP,
    input logic RST,
    input logic b0,
    input logic b1
);

property ResetSynceotid; @(posedge CLK) (RST) |-> C_reg == 8'b0 ;endproperty
assert property (ResetSynceotid);

property SubOnRsteotid; @(posedge CLK) (RST) != 1'b1 &&  (OP) == 1'b1  |-> C_reg == A - B ;endproperty
assert property (SubOnRsteotid);

property AddOnRsteotid; @(posedge CLK) (RST) != 1'b1 &&  (OP) != 1'b1  |-> C_reg == A + B ;endproperty
assert property (AddOnRsteotid);

endmodule