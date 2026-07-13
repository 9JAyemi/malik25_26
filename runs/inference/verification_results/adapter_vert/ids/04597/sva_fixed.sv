module mux_2_1_sva (
    input logic and_0,
    input logic in0,
    input logic in1,
    input logic out,
    input logic sel,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (sel) |-> (and_0) ;endproperty
assert property (ClockSynceotid);

property ValidIneotid; @(posedge clk_in_1) (sel) &&  (  ! (in0) &&  (in1)  ) |-> (out) ;endproperty
assert property (ValidIneotid);

property ValidIneotid_2; @(posedge clk_in_1) (sel) &&  (  (in0) &&  ! (in1)  ) |-> (out) ;endproperty
assert property (ValidIneotid_2);

endmodule