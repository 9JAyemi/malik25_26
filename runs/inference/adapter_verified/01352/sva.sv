module binary_to_gray_sva (
    input logic [3:0] in,
    input logic       load,
    input logic [3:0] out,
    input logic       valid
);

// On a load, valid is asserted on the next cycle.
    check_valid_asserts_after_load: assert property (
        @(posedge load) 1 |=> (valid == 1'b1)
    );

// On a load, out equals the previous cycle's in >> 1 ^ in.
    check_out_updates_after_load: assert property (
        @(posedge load) 1 |=> (out == ($past(in) >> 1) ^ $past(in))
    );

// When not loading, valid is deasserted on the next cycle.
    check_valid_deasserts_when_not_loading: assert property (
        @(posedge load) !load |=> (valid == 1'b0)
    );

// When not loading, out holds its previous value.
    check_out_holds_when_not_loading: assert property (
        @(posedge load) !load |=> (out == $past(out))
    );

endmodule
