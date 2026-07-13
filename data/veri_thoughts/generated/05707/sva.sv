module shift_register_assertions (
    input logic        clk,
    input logic        rst_n,
    input logic        load,
    input logic [7:0]  data_in,
    input logic [7:0]  data_out
);

    // Active-low reset clears the register output.
    check_reset_clears_data_out: assert property (
        @(posedge clk) !rst_n |-> (data_out == 8'h00)
    );

    // When load is high, the next output matches the input value.
    check_load_captures_data_in: assert property (
        @(posedge clk) disable iff (!rst_n)
        load |=> (data_out == $past(data_in))
    );

    // When load is low, the next output shifts left and inserts 0 in bit 0.
    check_shift_updates_data_out: assert property (
        @(posedge clk) disable iff (!rst_n)
        !load |=> (data_out == {$past(data_out[6:0]), 1'b0})
    );

    // A shift operation always drives the new LSB to 0.
    check_shift_inserts_zero_lsb: assert property (
        @(posedge clk) disable iff (!rst_n)
        !load |=> (data_out[0] == 1'b0)
    );

    // A shift operation moves prior bits [6:0] into current bits [7:1].
    check_shift_moves_upper_bits: assert property (
        @(posedge clk) disable iff (!rst_n)
        !load |=> (data_out[7:1] == $past(data_out[6:0]))
    );

endmodule