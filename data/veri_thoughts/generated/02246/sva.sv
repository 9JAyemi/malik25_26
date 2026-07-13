module ChooseModule_sva (
    input logic io_valid_0,
    input logic io_ready,
    input logic io_chosen
);
    // Output equals ~(io_ready & io_valid_0) when io_ready rises.
    check_equiv_on_posedge_ready: assert property (
        @(posedge io_ready) io_chosen == ~(io_ready & io_valid_0)
    );

    // Output equals ~(io_ready & io_valid_0) when io_valid_0 rises.
    check_equiv_on_posedge_valid: assert property (
        @(posedge io_valid_0) io_chosen == ~(io_ready & io_valid_0)
    );

    // If both inputs HIGH, output must be LOW (sampled on io_ready rise).
    check_low_when_both_high_on_ready: assert property (
        @(posedge io_ready) (io_ready && io_valid_0) |-> (io_chosen == 1'b0)
    );

    // If both inputs HIGH, output must be LOW (sampled on io_valid_0 rise).
    check_low_when_both_high_on_valid: assert property (
        @(posedge io_valid_0) (io_ready && io_valid_0) |-> (io_chosen == 1'b0)
    );

    // When io_ready is HIGH and io_valid_0 is LOW, output must be HIGH (on io_ready rise).
    check_high_when_ready_high_and_valid_low_on_ready: assert property (
        @(posedge io_ready) (io_ready && !io_valid_0) |-> (io_chosen == 1'b1)
    );

    // When io_ready is LOW, output must be HIGH (on io_valid_0 rise).
    check_high_when_ready_low_on_valid: assert property (
        @(posedge io_valid_0) (!io_ready) |-> (io_chosen == 1'b1)
    );

    // Output LOW implies both inputs are HIGH (sampled on io_ready rise).
    check_zero_implies_both_high_on_ready: assert property (
        @(posedge io_ready) (io_chosen == 1'b0) |-> (io_ready && io_valid_0)
    );

    // Output LOW implies both inputs are HIGH (sampled on io_valid_0 rise).
    check_zero_implies_both_high_on_valid: assert property (
        @(posedge io_valid_0) (io_chosen == 1'b0) |-> (io_ready && io_valid_0)
    );

    // Output HIGH implies not both inputs HIGH (sampled on io_ready rise).
    check_one_implies_not_both_high_on_ready: assert property (
        @(posedge io_ready) (io_chosen == 1'b1) |-> !(io_ready && io_valid_0)
    );

    // Output HIGH implies not both inputs HIGH (sampled on io_valid_0 rise).
    check_one_implies_not_both_high_on_valid: assert property (
        @(posedge io_valid_0) (io_chosen == 1'b1) |-> !(io_ready && io_valid_0)
    );
endmodule