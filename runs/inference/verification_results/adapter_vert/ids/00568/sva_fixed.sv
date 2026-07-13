module alu2_sva (
    input logic alucontrol,
    input logic aluflags,
    input logic aluresult,
    input logic cout,
    input logic srca,
    input logic srcb,
    input logic srcbc,
    input logic sum,
    input logic b0000,
    input logic b0010,
    input logic b10,
    input logic b11,
    input logic bxx10,
    input logic clk_in_12
);

property AddOneeotid; @(posedge clk_in_12) (alucontrol[0]) |-> (cout) == (srca) && (sum) == (srcbc) ; endproperty
assert property (AddOneeotid);

property AddOneeotid_2; @(posedge clk_in_12) (alucontrol[0]) |-> (aluresult) == (sum) ; endproperty
assert property (AddOneeotid_2);

property ANDeotid; @(posedge clk_in_12) (alucontrol) == (2'b10) |-> (aluresult) == (srca) && (aluresult) == (srcb) ; endproperty
assert property (ANDeotid);

property OReotid; @(posedge clk_in_12) (alucontrol) == (2'b11) |-> (aluresult) == (srca) || (aluresult) == (srcb) ; endproperty
assert property (OReotid);

property ValidReseteotid; @(posedge clk_in_12) (alucontrol[0]) |-> (aluflags) == (4'bxx10) ; endproperty
assert property (ValidReseteotid);

property ValidReseteotid_2; @(posedge clk_in_12) (alucontrol[0]) |-> (aluflags) == (4'b0010) ; endproperty
assert property (ValidReseteotid_2);

property ValidReseteotid_3; @(posedge clk_in_12) (alucontrol[0]) |-> (aluflags) != 4'b0000 ; endproperty
assert property (ValidReseteotid_3);

endmodule