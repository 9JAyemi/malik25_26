module binary_to_gray_sva (
    input logic in,
    input logic load,
    input logic out,
    input logic valid
);

property LoadSynceotid; @(posedge load) (load) |-> (out == (in >> 1) ^ in) && (valid == 1) ; endproperty
assert property (LoadSynceotid);

property ValidOnLoador; @(posedge load) (load) |-> (valid == 1) ; endproperty
assert property (ValidOnLoador);

property ValidOnLoador_2; @(posedge load) ! (load)  |-> (valid == 0) ; endproperty
assert property (ValidOnLoador_2);

endmodule