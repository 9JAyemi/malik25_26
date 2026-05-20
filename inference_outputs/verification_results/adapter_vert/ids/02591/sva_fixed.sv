module magnitude_comparator_sva (
    input logic A,
    input logic B,
    input logic out,
    input logic clk_in_1
);

property MagnitudeCheckeotid; @(posedge clk_in_1) ( |A ) && (  |B  ) |-> ( |A ) > (  |B  ) && (  out  == 1 ) ;endproperty
assert property (MagnitudeCheckeotid);

property ValidDataeotid; @(posedge clk_in_1) ( |A ) && (  |B  ) |-> ( |A ) <= (  |B  ) && (  out  == 0 ) ;endproperty
assert property (ValidDataeotid);

endmodule