module comparator_sva (
    input logic in0,
    input logic in0_reg,
    input logic in1,
    input logic in1_reg,
    input logic result,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic clk_in_19
);

property SyncCheckeotid; @(posedge clk_in_19) (in0) |-> in0_reg == in0 ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_19) (in1) |-> in1_reg == in1 ;endproperty
assert property (SyncCheckeotid_2);

property GreaterThaneotid; @(posedge clk_in_19) (in0) > (in1) |-> result == 2'b01 ;endproperty
assert property (GreaterThaneotid);

property LessThaneotid; @(posedge clk_in_19) (in0) < (in1) |-> result == 2'b10 ;endproperty
assert property (LessThaneotid);

property EqualCheckeotid; @(posedge clk_in_19) (in0) == (in1) |-> result == 2'b00 ;endproperty
assert property (EqualCheckeotid);

endmodule