// SVA for sky130_fd_sc_ls__clkdlyinv3sd1
// Bind-only assertions; no DUT modification required.

module sky130_fd_sc_ls__clkdlyinv3sd1_sva (
    input logic A,
    input logic Y
);

    // Functional equivalence (4-state accurate)
    always_comb
        assert (Y === ~A)
        else $error("sky130_fd_sc_ls__clkdlyinv3sd1: Y(%b) != ~A(%b)", Y, A);

    // Clean 0/1 transitions on A must invert at Y in the same delta and toggle Y
    property a_toggle_propagates;
        @(posedge A or negedge A) ##0 (Y === ~A && $changed(Y));
    endproperty
    assert property (a_toggle_propagates)
        else $error("A toggle did not invert/propagate to Y");

    // Y must not toggle unless A toggles
    property y_no_spurious_toggles;
        @(posedge Y or negedge Y) $changed(A);
    endproperty
    assert property (y_no_spurious_toggles)
        else $error("Y toggled without A changing");

    // Known input implies known, inverted output
    property known_in_known_out;
        @(A) (!$isunknown(A)) |-> (!$isunknown(Y) && Y === ~A);
    endproperty
    assert property (known_in_known_out)
        else $error("Known A did not produce known inverted Y");

    // X/Z on input must propagate to X on output (primitive ~X/~Z => X)
    property xz_propagates;
        @(A) ($isunknown(A)) |-> $isunknown(Y);
    endproperty
    assert property (xz_propagates)
        else $error("Unknown/Z on A did not propagate to Y");

    // Coverage: hit both levels and both polarities, and X-propagation
    cover property (@(A) (A==1'b0 && Y==1'b1));
    cover property (@(A) (A==1'b1 && Y==1'b0));
    cover property (@(posedge A) ##0 (Y==1'b0));
    cover property (@(negedge A) ##0 (Y==1'b1));
    cover property (@(A) ($isunknown(A) && $isunknown(Y)));

endmodule

bind sky130_fd_sc_ls__clkdlyinv3sd1 sky130_fd_sc_ls__clkdlyinv3sd1_sva sva_i (.A(A), .Y(Y));