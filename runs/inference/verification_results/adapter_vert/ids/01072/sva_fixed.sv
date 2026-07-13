module full_adder_sva (
    input logic A,
    input logic B,
    input logic C_out,
    input logic Cin,
    input logic S,
    input logic clk_in_1
);

property AdderSynceotid; @(posedge clk_in_1) (A) |-> (S) ; endproperty
assert property (AdderSynceotid);

property AdderSynceotid_2; @(posedge clk_in_1) (A) &&  (B) &&  (Cin) |-> (C_out) ; endproperty
assert property (AdderSynceotid_2);

property AdderSynceotid_3; @(posedge clk_in_1) (A) &&  (B) &&  (!Cin) |-> (C_out) ; endproperty
assert property (AdderSynceotid_3);

property AdderSynceotid_4; @(posedge clk_in_1) (A) &&  (!B) &&  (Cin) |-> (C_out) ; endproperty
assert property (AdderSynceotid_4);

property AdderSynceotid_5; @(posedge clk_in_1) (A) &&  (!B) &&  (!Cin) |-> (S) ; endproperty
assert property (AdderSynceotid_5);

property AdderSynceotid_6; @(posedge clk_in_1) (!A) &&  (B) &&  (Cin) |-> (C_out) ; endproperty
assert property (AdderSynceotid_6);

property AdderSynceotid_7; @(posedge clk_in_1) (!A) &&  (B) &&  (!Cin) |-> (S) ; endproperty
assert property (AdderSynceotid_7);

property AdderSynceotid_8; @(posedge clk_in_1) (!A) &&  (!B) &&  (Cin) |-> (C_out) ; endproperty
assert property (AdderSynceotid_8);

property AdderSynceotid_9; @(posedge clk_in_1)  (A) &&  (B)  &&  (Cin)  &&  (  !S  &&  !C_out ) |->  (  !A  || !B  || !Cin )  ; endproperty
assert property (AdderSynceotid_9);

property AdderSynceotid_10; @(posedge clk_in_1)  (A) &&  (B)  &&  (!Cin)  &&  (  !S  &&  C_out ) |->  (  !A  || !B  || Cin )  ; endproperty
assert property (AdderSynceotid_10);

property AdderSynceotid_11; @(posedge clk_in_1)  (A) &&  (!B)  &&  (Cin)  &&  (  S  &&  !C_out ) |->  (  !A  || B  || !Cin )  ; endproperty
assert property (AdderSynceotid_11);

property AdderSynceotid_12; @(posedge clk_in_1)  (A) &&  (!B)  &&  (!Cin)  &&  (  S  &&  C_out ) |->  (  A  &&  !B  &&  !Cin )  ; endproperty
assert property (AdderSynceotid_12);

property AdderSynceotid_13; @(posedge clk_in_1)  (!A) &&  (B)  &&  (Cin)  &&  (  !S  &&  C_out ) |->  (  A  || !B  || !Cin )  ; endproperty
assert property (AdderSynceotid_13);

property AdderSynceotid_14; @(posedge clk_in_1)  (!A) &&  (B)  &&  (!Cin)  &&  (  S  &&  !C_out ) |->  (  A  || !B  &&  !Cin )  ; endproperty
assert property (AdderSynceotid_14);

property AdderSynceotid_15; @(posedge clk_in_1)  (!A) &&  (!B)  &&  (Cin)  &&  (  !S  &&  C_out ) |->  (  A  || B  || !Cin )  ; endproperty
assert property (AdderSynceotid_15);

property AdderSynceotid_16; @(posedge clk_in_1)  (A) &&  (B)  &&  (Cin)  &&  (  S  &&  C_out ) |->  (  !A  && !B  && !Cin )  ; endproperty
assert property (AdderSynceotid_16);

endmodule