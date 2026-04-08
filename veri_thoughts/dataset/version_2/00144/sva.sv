module reg_unit_sva #(parameter ff_sz = 8) (
    input logic [ff_sz-1:0] data_out,
    input logic [ff_sz-1:0] data_in,
    input logic load,
    input logic clk,
    input logic rst
);

    // Active-low reset drives the register to zero by the next sampled cycle.
    check_reset_clears_data_out: assert property (
        @(posedge clk) !rst |=> (data_out == '0)
    );

    // When load is high, the register captures data_in on the next cycle.
    check_load_captures_data_in: assert property (
        @(posedge clk) disable iff (!rst) load |=> (data_out == $past(data_in))
    );

    // When load is low, the register holds its previous value.
    check_hold_when_load_low: assert property (
        @(posedge clk) disable iff (!rst) !load |=> (data_out == $past(data_out))
    );

endmodule