module dff_en_assertions (
    input logic D,
    input logic C,
    input logic E,
    input logic Q
);

    // An enabled rising edge loads D into Q.
    check_load_on_enable: assert property (
        @(posedge C) E |=> (Q == $past(D))
    );

    // A disabled rising edge leaves Q unchanged.
    check_hold_on_disable: assert property (
        @(posedge C) !E |=> (Q == $past(Q))
    );

    // Enabled new data must change Q on the next sampled cycle.
    check_change_on_new_enabled_data: assert property (
        @(posedge C) (E && (D != Q)) |=> (Q != $past(Q))
    );

    // Enabled same data must leave Q unchanged.
    check_no_change_on_same_enabled_data: assert property (
        @(posedge C) (E && (D == Q)) |=> (Q == $past(Q))
    );

endmodule