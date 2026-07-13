module shift_register_sva (
    input logic data_in,
    input logic q0,
    input logic q1,
    input logic q2,
    input logic q3,
    input logic reset,
    input logic shift_clk,
    input logic b0000
);

property ResetSynceotid; @(posedge shift_clk) (reset) |-> (q0 == 4'b0000) && (q1 == 4'b0000) && (q2 == 4'b0000) && (q3 == 4'b0000) ;endproperty
assert property (ResetSynceotid);

property ShiftSynceotid; @(posedge shift_clk) ( !reset ) |-> (q0 == data_in) && (q1 == q0) && (q2 == q1) && (q3 == q2) ;endproperty
assert property (ShiftSynceotid);

endmodule