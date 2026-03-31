module shift_register_sva (
    input logic       clk,
    input logic       load,
    input logic [3:0] data_in,
    input logic [3:0] data_out
);

// Load captures data_in on the next cycle.
    check_load_captures_data: assert property (
        @(posedge clk) load |=> (data_out == $past(data_in))
    );

// Without load, the register shifts left and inserts 0 in bit 0.
    check_shift_left_when_not_load: assert property (
        @(posedge clk) !load |=> (data_out == {$past(data_out[2:0]), 1'b0})
    );

// Bit 3 follows bit 2 when not loading.
    check_bit3_follows_bit2: assert property (
        @(posedge clk) !load |=> (data_out[3] == $past(data_out[2]))
    );

// Bit 2 follows bit 1 when not loading.
    check_bit2_follows_bit1: assert property (
        @(posedge clk) !load |=> (data_out[2] == $past(data_out[1]))
    );

// Bit 1 follows bit 0 when not loading.
    check_bit1_follows_bit0: assert property (
        @(posedge clk) !load |=> (data_out[1] == $past(data_out[0]))
    );

// Bit 0 is cleared when not loading.
    check_bit0_is_zero: assert property (
        @(posedge clk) !load |=> (data_out[0] == 1'b0)
    );

endmodule
