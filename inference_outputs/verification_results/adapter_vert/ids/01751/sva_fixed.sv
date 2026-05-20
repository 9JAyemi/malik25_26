module c_clkgate_sva (
    input logic active,
    input logic active_q,
    input logic clk,
    input logic clk_gated
);

property ClockSynceotid; @(posedge clk) (clk) |-> (active) == (active_q) ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk) (clk) &&  (  ! ( clk ) &&  (  active ) ) |->  (  clk_gated )  ;endproperty
assert property (ClockSynceotid_2);

endmodule