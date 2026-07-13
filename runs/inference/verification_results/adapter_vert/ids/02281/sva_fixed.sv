module mux_priority_encoder_sva (
    input logic a,
    input logic b,
    input logic in,
    input logic mux_out,
    input logic out_sum,
    input logic pos,
    input logic sel_b1,
    input logic sel_b2,
    input logic b000,
    input logic b0000000,
    input logic b0000001,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (a) && (b) |-> (mux_out) == (b) ; endproperty
assert property (ClockSynceotid);

property ValidInputeotid; @(posedge clk_in_1) (a) && ! (b)  &&  (sel_b1)  &&  (sel_b2)  ||  ! (a)  &&  (b)  &&  (sel_b1)  &&  (sel_b2)  ||  ! (a)  && ! (b)  &&  ! (sel_b1)  &&  ! (sel_b2)  == (mux_out); endproperty
assert property (ValidInputeotid);

property ValidIneotid; @(posedge clk_in_1) (in) != 7'b0000000 |-> pos == 3'b000 ; endproperty
assert property (ValidIneotid);

property ValidIneotid_2; @(posedge clk_in_1) (in) == 7'b0000001  &&  (sel_b1)  &&  (sel_b2)  ||  (in) != 7'b0000001  &&  ! (sel_b1)  &&  (sel_b2)  ||  (in) != 7'b0000001  &&  (sel_b1)  &&  ! (sel_b2)  ||  (in) != 7'b0000001  && ! (sel_b1)  && ! (sel_b2)  == (pos); endproperty
assert property (ValidIneotid_2);

property ValidIneotid_3; @(posedge clk_in_1) (in) != 7'b0000000  &&  (pos) == 3'b000  |-> (out_sum) == (mux_out) ; endproperty
assert property (ValidIneotid_3);

property ValidIneotid_4; @(posedge clk_in_1) (in) == 7'b0000001  &&  (sel_b1)  &&  (sel_b2)  ||  (in) != 7'b0000001  &&  ! (sel_b1)  &&  (sel_b2)  ||  (in) != 7'b0000001  &&  (sel_b1)  &&  ! (sel_b2)  ||  (in) != 7'b0000001  && ! (sel_b1)  && ! (sel_b2)  == (out_sum); endproperty
assert property (ValidIneotid_4);

endmodule