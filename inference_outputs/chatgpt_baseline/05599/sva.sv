module rotation_module_sva (
    input logic        clk,
    input logic        reset,
    input logic [3:0]  in,
    input logic        load,
    input logic        select,
    input logic [15:0] data,
    input logic [3:0]  out
);

    // Reset drives out to zero.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |-> (out == 4'b0000)
    );

    // Load updates out from data[3:0].
    check_load_updates_out: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (out == $past(data[3:0]))
    );

    // Load has priority over select.
    check_load_priority_over_select: assert property (
        @(posedge clk) disable iff (reset)
        (load && select) |=> (out == $past(data[3:0]))
    );

    // Select rotates in when load is low.
    check_select_rotation: assert property (
        @(posedge clk) disable iff (reset)
        (!load && select) |=> (out == $past({in[2:0], in[3]}))
    );

    // Default path rotates in when both controls are low.
    check_default_rotation: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !select) |=> (out == $past({in[0], in[3:1]}))
    );

    // Every non-reset cycle follows the RTL next-state function.
    check_next_state_function: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (
            out == ($past(load) ? $past(data[3:0]) :
                    ($past(select) ? $past({in[2:0], in[3]}) :
                                     $past({in[0], in[3:1]})))
        )
    );

endmodule