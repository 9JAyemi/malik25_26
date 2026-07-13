module counter_sva (
    input logic clk,
    input logic count,
    input logic enable,
    input logic overflow,
    input logic reset,
    input logic b0,
    input logic b0000,
    input logic b1,
    input logic b1111
);

property ResetSynceotid; @(posedge clk) (reset) |-> (count == 4'b0000) && (overflow == 1'b0) ;endproperty
assert property (ResetSynceotid);

property SafeCtrleotid; @(posedge clk) (reset) |-> (count != 4'b1111) ;endproperty
assert property (SafeCtrleotid);

property SafeCtrleotid_2; @(posedge clk) (enable) &&  (  ! (reset)  &&  ! (count == 4'b1111)  ) |-> count == (count + 1) ;endproperty
assert property (SafeCtrleotid_2);

property ResetSynceotid_2; @(posedge clk) (enable) &&  (  ! (reset)  &&  (count == 4'b1111)  ) |-> (count == 4'b0000) && (overflow == 1'b1) ;endproperty
assert property (ResetSynceotid_2);

endmodule