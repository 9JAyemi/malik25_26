module dffsi_4_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] init,
    input logic [3:0] d,
    input logic [3:0] q
);

    // A reset clock edge loads q from init.
    check_reset_loads_init: assert property (
        @(posedge clk) reset |=> (q == $past(init))
    );

    // A non-reset clock edge loads q from d.
    check_data_loads_d: assert property (
        @(posedge clk) (!reset) |=> (q == $past(d))
    );

    // Across consecutive non-reset cycles, q continues to follow d.
    check_data_loads_d_across_non_reset_cycles: assert property (
        @(posedge clk) disable iff (reset) (!reset) |=> (!reset && (q == $past(d)))
    );

    // q always matches the source selected on the previous clock edge.
    check_selected_input_update: assert property (
        @(posedge clk) 1'b1 |=> (q == $past(reset ? init : d))
    );

endmodule