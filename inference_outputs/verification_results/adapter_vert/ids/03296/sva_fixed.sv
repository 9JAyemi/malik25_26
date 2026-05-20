module compare_signed_mag_sva (
    input logic A,
    input logic B,
    input logic equal,
    input logic out,
    input logic shifted_num,
    input logic signed_larger,
    input logic signed_smaller,
    input logic smaller_num,
    input logic clk_in_14
);

property SyncEqeotid; @(posedge clk_in_14) (A) == (B) |-> (equal) ; endproperty
assert property (SyncEqeotid);

property PosSynceotid; @(posedge clk_in_14) (A) != (B) &&  (  $signed (A)  >  $signed (B)  ) |-> (signed_larger) ; endproperty
assert property (PosSynceotid);

property SignedSmalleotid; @(posedge clk_in_14) (A) != (B) &&  (  $signed (A)  <  $signed (B)  ) |-> (signed_smaller) ; endproperty
assert property (SignedSmalleotid);

property SyncCheckeotid; @(posedge clk_in_14) (A) == (B) |->  (  out  ==  0 ) ; endproperty
assert property (SyncCheckeotid);

property ShiftOnRiseeotid; @(posedge clk_in_14) (A) != (B) &&  (  $signed (A)  >  $signed (B)  ) |->  (  out  ==  shifted_num ) ; endproperty
assert property (ShiftOnRiseeotid);

property SyncCheckeotid_2; @(posedge clk_in_14) (A) != (B) &&  (  $signed (A)  <  $signed (B)  ) |->  (  out  ==  smaller_num ) ; endproperty
assert property (SyncCheckeotid_2);

endmodule