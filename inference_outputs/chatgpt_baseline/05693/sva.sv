module shift_register_sva (
    input logic clk,
    input logic load,
    input logic [3:0] data_in,
    input logic [3:0] data_out
);

    // When load is high, bit 3 captures input bit 3 on the next clock.
    check_load_captures_bit3: assert property (
        @(posedge clk) load |=> data_out[3] == $past(data_in[3])
    );

    // When load is high, bit 2 captures input bit 2 on the next clock.
    check_load_captures_bit2: assert property (
        @(posedge clk) load |=> data_out[2] == $past(data_in[2])
    );

    // When load is high, bit 1 captures input bit 1 on the next clock.
    check_load_captures_bit1: assert property (
        @(posedge clk) load |=> data_out[1] == $past(data_in[1])
    );

    // When load is high, bit 0 captures input bit 0 on the next clock.
    check_load_captures_bit0: assert property (
        @(posedge clk) load |=> data_out[0] == $past(data_in[0])
    );

    // When load is low, bit 3 takes the previous bit 2 on the next clock.
    check_rotate_bit3_from_bit2: assert property (
        @(posedge clk) !load |=> data_out[3] == $past(data_out[2])
    );

    // When load is low, bit 2 takes the previous bit 1 on the next clock.
    check_rotate_bit2_from_bit1: assert property (
        @(posedge clk) !load |=> data_out[2] == $past(data_out[1])
    );

    // When load is low, bit 1 takes the previous bit 0 on the next clock.
    check_rotate_bit1_from_bit0: assert property (
        @(posedge clk) !load |=> data_out[1] == $past(data_out[0])
    );

    // When load is low, bit 0 takes the previous bit 3 on the next clock.
    check_rotate_bit0_from_bit3: assert property (
        @(posedge clk) !load |=> data_out[0] == $past(data_out[3])
    );

endmodule