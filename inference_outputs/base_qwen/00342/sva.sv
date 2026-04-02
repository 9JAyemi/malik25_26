module shift_register_sva (
    input logic clk,
    input logic shift_dir,
    input logic parallel_load,
    input logic [7:0] data_in,
    output logic [7:0] serial_out,
    output logic [7:0] parallel_out
);
    // Sequential logic for shift register
    // Shift register should update on the rising edge of the clock
    shift_reg_update: assert property (
        @(posedge clk) disable iff (!clk) $stable(shift_reg)
    );

    // Parallel load should update the shift register on the rising edge of the clock
    parallel_load_update: assert property (
        @(posedge clk) disable iff (!clk) parallel_load |-> shift_reg == data_in
    );

    // Serial output should be the least significant bit of the shift register
    serial_output_check: assert property (
        @(posedge clk) disable iff (!clk) serial_out == shift_reg[0]
    );

    // Parallel output should be the entire shift register
    parallel_output_check: assert property (
        @(posedge clk) disable iff (!clk) parallel_out == shift_reg
    );

    // Shift direction should affect the shift register content
    shift_direction_check: assert property (
        @(posedge clk) disable iff (!clk) shift_dir |-> shift_reg[6:0] == shift_reg[6:0] && shift_reg[7] == 1'b0
    );

    // Shift direction should affect the shift register content
    shift_direction_check_2: assert property (
        @(posedge clk) disable iff (!clk) !shift_dir |-> shift_reg[0] == 1'b0 && shift_reg[7:1] == shift_reg[7:1]
    );

    // Shift register should not change when not parallel loaded or shifting
    shift_register_stable: assert property (
        @(posedge clk) disable iff (!clk) !(parallel_load || shift_dir) |-> $stable(shift_reg)
    );

    // Parallel load should not change the shift register when not parallel loaded
    parallel_load_stable: assert property (
        @(posedge clk) disable iff (!clk) !parallel_load |-> $stable(shift_reg)
    );

    // Shift direction should not change the shift register when not shifting
    shift_direction_stable: assert property (
        @(posedge clk) disable iff (!clk) !shift_dir |-> $stable(shift_reg)
    );

    // Shift register should not change when not parallel loaded or shifting
    shift_register_stable_2: assert property (
        @(posedge clk) disable iff (!clk) !(parallel_load || shift_dir) |-> $stable(shift_reg)
    );

    // Parallel load should not change the shift register when not parallel loaded
    parallel_load_stable_2: assert property (
        @(posedge clk) disable iff (!clk) !parallel_load |-> $stable(shift_reg)
    );

    // Shift direction should not change the shift register when not shifting
    shift_direction_stable_2: assert property (
        @(posedge clk) disable iff (!clk) !shift_dir |-> $stable(shift_reg)
    );
endmodule