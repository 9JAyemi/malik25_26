module test_in_sva (
    input logic activate,
    input logic clk,
    input logic count,
    input logic data,
    input logic enable,
    input logic ready,
    input logic rst,
    input logic strobe
);

property ResetSynceotid; @(posedge clk) (rst) |-> (activate == 0) && (data == 0) && (strobe == 0) && (count == 0) ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (rst) |-> (strobe == 0) ;endproperty
assert property (ResetSynceotid_2);

property ReadySynceotid; @(posedge clk) (rst) &&  ( (ready > 0) && (activate == 0) && enable )  |->  (count == 0) && (  (ready[0]) && (  activate[0] == 1 )  ) ;endproperty
assert property (ReadySynceotid);

property ReadySynceotid_2; @(posedge clk) (rst) &&  ( (ready > 0) && (activate == 0) && enable )  &&  ( !(ready[0])  )  |->  (  activate[1] == 1 ) ;endproperty
assert property (ReadySynceotid_2);

property ActiveSynceotid; @(posedge clk) ! (rst)  &&  (  (ready > 0) && (activate == 0) && enable  ) |->  (  data  ==  count ) && (  count  ==  (  data  +  1 )  ) && (  strobe  ==  1 ) ;endproperty
assert property (ActiveSynceotid);

property SafeReseteotid; @(posedge clk) ! (rst)  &&  (  (ready > 0) && (activate == 0) && enable  )  &&  (  (ready > 0) && (activate == 0) && enable  ) &&  (  activate > 0  )  |->  (  activate  !=  0 ) ;endproperty
assert property (SafeReseteotid);

property ResetSynceotid_3; @(posedge clk) ! (rst)  &&  (  !(ready > 0)  &&  (  activate > 0  )  ) |->  (  activate  ==  0 ) ;endproperty
assert property (ResetSynceotid_3);

endmodule