module shift_register_sva (
    input logic        clk,
    input logic        load,
    input logic [3:0]  data_in,
    input logic [3:0]  data_out
);
    // Clock: clk posedge; no reset; sequential shift-left with parallel load.

    // On load, next data_out equals the sampled data_in.
    check_parallel_load_next_out: assert property (
        @(posedge clk) load |=> (data_out == $past(data_in))
    );

    // On no-load, next LSB is forced to 0.
    check_shift_lsb_zero_each_no_load: assert property (
        @(posedge clk) (!load) |=> (data_out[0] == 1'b0)
    );

    // On no-load, next upper bits mirror prior lower bits when known.
    check_shift_upper_bits_when_known: assert property (
        @(posedge clk) (!load && !$isunknown(data_out[2:0])) |=> (data_out[3:1] == $past(data_out[2:0]))
    );

    // Two consecutive no-load cycles force next two LSBs to 0.
    check_two_no_loads_zero_lsb2: assert property (
        @(posedge clk) (!load)[*2] |=> (data_out[1:0] == 2'b00)
    );

    // Three consecutive no-load cycles force next three LSBs to 0.
    check_three_no_loads_zero_lsb3: assert property (
        @(posedge clk) (!load)[*3] |=> (data_out[2:0] == 3'b000)
    );

    // Four consecutive no-load cycles clear the register to 0.
    check_four_no_loads_zero_all: assert property (
        @(posedge clk) (!load)[*4] |=> (data_out == 4'b0000)
    );

    // Load followed by no-load shifts the loaded value left with 0 inserted.
    check_load_then_shift_of_loaded_data: assert property (
        @(posedge clk) (load ##1 !load) |=> (data_out == {$past(data_in,2)[2:0], 1'b0})
    );

    // Back-to-back loads: second load determines the output.
    check_back_to_back_loads_last_wins: assert property (
        @(posedge clk) (load ##1 load) |=> (data_out == $past(data_in,1))
    );

    // With no-load and zero value, next value remains zero.
    check_zero_sticky_without_load: assert property (
        @(posedge clk) (!load && (data_out == 4'b0000)) |=> (data_out == 4'b0000)
    );

endmodule