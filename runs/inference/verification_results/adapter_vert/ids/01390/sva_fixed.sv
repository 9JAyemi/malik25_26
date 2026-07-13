module csa_generate_adder_32bit_sva (
    input logic A,
    input logic B,
    input logic Cin,
    input logic Cout,
    input logic S,
    input logic clk_in_17
);

property AdderSynceotid; @(posedge clk_in_17) (A) |-> (S) ;endproperty
assert property (AdderSynceotid);

property CarrySynceotid; @(posedge clk_in_17) (A) &&  (B) &&  (Cin) |->  (Cout) ;endproperty
assert property (CarrySynceotid);

property CarrySynceotid_2; @(posedge clk_in_17) (A) &&  (B) &&  (!Cin) |->  (Cout) ;endproperty
assert property (CarrySynceotid_2);

property CarrySynceotid_3; @(posedge clk_in_17) (A) &&  (!B) &&  (Cin) |->  (Cout) ;endproperty
assert property (CarrySynceotid_3);

property CarrySynceotid_4; @(posedge clk_in_17) (A) &&  (!B) &&  (!Cin) |->  (Cout) ;endproperty
assert property (CarrySynceotid_4);

property AdderSynceotid_2; @(posedge clk_in_17) (A) ||  (B) ||  (Cin) |->  (S) ;endproperty
assert property (AdderSynceotid_2);

property SyncAddereotid; @(posedge clk_in_17) (A) ||  (B) ||  (Cin) &&  (  ! (A)  || ! (B)  ||  (Cout) ) |->  (S) ;endproperty
assert property (SyncAddereotid);

property SyncAddereotid_2; @(posedge clk_in_17) (A) ||  (B) ||  (Cin) &&  (  ! (A)  || ! (B)  ||  (Cout) ) &&  (  ! (A)  ||  (B)  ||  (Cout) ) |->  (S) ;endproperty
assert property (SyncAddereotid_2);

property yncAddereotid; @(posedge clk_in_17) (A) ||  (B) ||  (Cin) &&  (  ! (A)  || ! (B)  ||  (Cout) ) &&  (  ! (A)  ||  (B)  ||  (Cout) ) &&  (  (A)  &&  (B)  &&  (Cin)  ||  (  ! (A)  && ! (B)  &&  (Cout)  ) ) |->  (S) ;endproperty
assert property (yncAddereotid);

endmodule