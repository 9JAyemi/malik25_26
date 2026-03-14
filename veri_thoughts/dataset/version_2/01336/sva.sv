module shift_register_sva (
    input logic clk,
    input logic reset,      // synchronous, active-high
    input logic load,
    input logic [3:0] data_in,
    input logic [3:0] data_out
);
    // Reset sets output to 0 on the next cycle.
    reset_clears_next: assert property (
        @(posedge clk) reset |=> (data_out == 4'b0000)
    );

    // While reset remains asserted, output stays 0.
    reset_holds_zero: assert property (
        @(posedge clk) $past(reset) && reset |-> (data_out == 4'b0000)
    );

    // When load is asserted, next output equals current data_in.
    load_updates_output: assert property (
        @(posedge clk) disable iff (reset) load |=> (data_out == $past(data_in))
    );

    // When not loading, next output is left-shift of current output with serial-in from data_in[3].
    shift_updates_output: assert property (
        @(posedge clk) disable iff (reset) !load |=> (data_out == { $past(data_out[2:0]), $past(data_in[3]) })
    );

    // When not loading, MSB shifts from previous bit[2].
    shift_msb_from_bit2: assert property (
        @(posedge clk) disable iff (reset) !load |=> (data_out[3] == $past(data_out[2]))
    );

    // When not loading, LSB takes data_in[3] of the same cycle.
    shift_lsb_from_datain_msb: assert property (
        @(posedge clk) disable iff (reset) !load |=> (data_out[0] == $past(data_in[3]))
    );
endmodule